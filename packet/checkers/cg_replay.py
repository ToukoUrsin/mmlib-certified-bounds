"""Cold exact dual/Farkas tree verification from raw original constraints."""
from __future__ import annotations
import argparse,copy,csv,hashlib,importlib.util,json,time
from collections import Counter
from pathlib import Path
from urllib.request import Request,urlopen
from raw_check import parse_mm,build_rows,check_witness,original_domains
from CG_check import cut_rows


def leaf(raw,H,cert,domains,global_rows=None):
    rows,upper,cols=build_rows(raw,H,domains)
    if global_rows is not None:rows=global_rows
    family=cert.get('row_family')
    if family not in ['precedence_energy_v1','precedence_energy_infeasible_v1']:raise ValueError('row family')
    D=cert.get('denominator');ys=cert.get('inequality_dual_integers');zs=cert.get('equality_dual_integers')
    if type(D)is not int or D<=0 or len(ys)!=len(rows)or len(zs)!=raw['n']:raise ValueError('dimensions')
    if any(type(y)is not int or y>0 for y in ys)or any(type(z)is not int for z in zs):raise ValueError('dual sign/type')
    residual=[0]*len(upper)
    if family=='precedence_energy_v1':residual[raw['n']-1]=D
    value=0
    for (entries,b),y in zip(rows,ys):
        value+=b*y
        for v,a in entries:residual[v]-=a*y
    for j,z in enumerate(zs,1):
        value+=z
        for k in range(len(raw['modes'][j])):residual[cols[j,k]]-=z
    value+=sum(min(0,r)*u for r,u in zip(residual,upper))
    if type(cert.get('claimed_numerator'))is not int or value!=cert['claimed_numerator']:raise ValueError('numerator differs')
    if family=='precedence_energy_infeasible_v1':
        if value<=0:raise ValueError('Farkas contradiction not strictly positive')
        return H+1
    return (value+D-1)//D


def verify(path,H,witness,tree):
    raw=parse_mm(Path(path));check_witness(raw,witness,H);counts=Counter()
    global_rows=None
    if 'CG_cuts'in tree:
        global_rows,_,cols=cut_rows(raw,H,tree['CG_cuts'])
        counts['CG_cuts']=len(tree['CG_cuts'])
        point=witness['starts']+[int(m[0]==witness['mode_ids'][j-1])for j in range(1,raw['n']+1)for m in raw['modes'][j]]
        if any(sum(a*point[v]for v,a in entries)>b for entries,b in global_rows):
            raise ValueError('original feasible witness violates a reconstructed CG row')
    def visit(node,domains):
        if set(node)=={'leaf_certificate'}:
            counts['leaves']+=1;counts[node['leaf_certificate']['row_family']]+=1
            return leaf(raw,H,node['leaf_certificate'],domains,global_rows)
        if set(node)!={'job_id','mode_id','included','excluded'}:raise ValueError('node fields')
        j,mid=node['job_id'],node['mode_id']
        if type(j)is not int or type(mid)is not int or not 1<=j<=raw['n']or mid not in domains[j-1]or len(domains[j-1])<2:
            raise ValueError('partition outside original inherited domain')
        inc=copy.deepcopy(domains);exc=copy.deepcopy(domains);inc[j-1]=[mid];exc[j-1]=[m for m in exc[j-1]if m!=mid]
        counts['splits']+=1
        return min(visit(node['included'],inc),visit(node['excluded'],exc))
    bound=visit(tree['root'],original_domains(raw))
    if tree.get('claimed_lb')!=bound or bound>H:raise ValueError('global claim/witness mismatch')
    return {'integer_makespan_lb':bound,**dict(counts),'input_sha256':hashlib.sha256(Path(path).read_bytes()).hexdigest()}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('directory',type=Path);args=ap.parse_args();out=args.directory;start=time.monotonic()
    claim=json.loads((out/'claim.json').read_text());tree=json.loads((out/'tree.json').read_text());witness=json.loads((out/'witness.json').read_text())
    path=Path('data/mmlib/plus')/claim['instance'];H=claim['H'];got=verify(path,H,witness,tree)
    if got['integer_makespan_lb']!=claim['new_LB']or got['input_sha256']!=claim['input_sha256']:raise ValueError('claim/source mismatch')
    controls=[]
    def reject(label,t,w=witness):
        try:verify(path,H,w,t)
        except(ValueError,TypeError,KeyError):controls.append(label)
        else:raise AssertionError('negative accepted: '+label)
    bad=copy.deepcopy(tree);bad['claimed_lb']+=1;reject('global_claim',bad)
    bad=copy.deepcopy(tree);node=bad['root']
    while 'leaf_certificate'not in node:node=node['included']
    node['leaf_certificate']['claimed_numerator']+=1;reject('leaf_numerator',bad)
    if 'mode_id'in tree['root']:
        bad=copy.deepcopy(tree);bad['root']['mode_id']=-1;reject('source_partition',bad)
    if tree.get('CG_cuts'):
        bad=copy.deepcopy(tree);bad['CG_cuts'][0]['denominator']=0;reject('CG_denominator',bad)
        bad=copy.deepcopy(tree);bad['CG_cuts'][0]['original_row_multipliers'].append([999999,1]);reject('CG_source_row',bad)
        bad=copy.deepcopy(tree)
        # Mutate an actual inequality weight so this checks the sign rule.
        original_count=len(build_rows(parse_mm(path),H)[0]);changed=False
        for pair in bad['CG_cuts'][0]['original_row_multipliers']:
            if pair[0]<original_count:pair[1]=-abs(pair[1])-1;changed=True;break
        if not changed:bad['CG_cuts'][0]['original_row_multipliers'].append([0,-1])
        reject('CG_inequality_sign',bad)
    def find_farkas(node):
        if 'leaf_certificate'in node:return node if node['leaf_certificate']['row_family']=='precedence_energy_infeasible_v1'else None
        return find_farkas(node['included'])or find_farkas(node['excluded'])
    bad=copy.deepcopy(tree);node=find_farkas(bad['root'])
    if node:
        c=node['leaf_certificate'];c['inequality_dual_integers']=[0]*len(c['inequality_dual_integers']);c['equality_dual_integers']=[0]*len(c['equality_dual_integers']);c['claimed_numerator']=0
        reject('nonpositive_Farkas_margin',bad)
    badw=copy.deepcopy(witness);badw['mode_ids'][0]=99999;reject('witness',tree,badw)
    URL='http://solutionsupdate.ugent.be/sites/default/files/datasets/MMplus_2.csv'
    data=urlopen(Request(URL,headers={'User-Agent':'shutdown-schedule-worker/021'}),timeout=30).read();(out/'MMplus_2.current.csv').write_bytes(data)
    lines=data.decode('latin1').splitlines();begin=next(i for i,line in enumerate(lines)if line.startswith('ID;'))
    vals=[r for r in csv.DictReader(lines[begin:],delimiter=';')if r.get('ID','').isdigit()and r.get('Ref1')]
    names=[r['Ref1']for r in vals]
    if len(names)!=len(set(names)):raise ValueError('duplicate live names')
    r=next(r for r in vals if r.get('Ref1')==claim['instance']);lb=int(r['LB value']);ub=int(r['UB value'])
    if not lb<got['integer_makespan_lb']<=ub:raise ValueError('fresh strict gate')
    evidence={'checked':got,'previous_LB':claim['previous_LB'],'extra_units':got['integer_makespan_lb']-claim['previous_LB'],
        'live_url':URL,'live_sha256':hashlib.sha256(data).hexdigest(),'live_LB':lb,'live_UB':ub,'delta_vs_live':got['integer_makespan_lb']-lb,
        'local_horizon_optimality':got['integer_makespan_lb']==H,'negative_controls_rejected':controls,
        'seconds':time.monotonic()-start,'evidence':'independent exact dual/Farkas replay; not submitted or accepted'}
    (out/'verification.json').write_text(json.dumps(evidence,indent=2)+'\n');print(json.dumps(evidence,indent=2))


if __name__=='__main__':main()
