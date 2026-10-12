"""Standard-library exact CG cut and dual replay from the original .mm."""
from __future__ import annotations
import argparse, copy, csv, hashlib, json, time
from collections import defaultdict
from pathlib import Path
from urllib.request import Request,urlopen
from raw_check import parse_mm,build_rows,check_witness


def cut_rows(raw,H,cuts):
    rows,upper,columns=build_rows(raw,H)
    original=rows.copy()
    for j in range(1,raw['n']+1):
        original.append(([(columns[j,k],1)for k in range(len(raw['modes'][j]))],1))
    original.extend(([(j,1)],u)for j,u in enumerate(upper))
    first_eq=len(rows);last_eq=first_eq+raw['n'];constructed=[]
    for cut in cuts:
        if set(cut)!={'denominator','original_row_multipliers'}:
            raise ValueError('CG cut fields')
        D=cut['denominator'];weights=cut['original_row_multipliers']
        if type(D)is not int or D<=0 or not isinstance(weights,list):
            raise ValueError('CG denominator/weights')
        coeff=defaultdict(int);rhs=0;seen=set()
        for pair in weights:
            if not isinstance(pair,list)or len(pair)!=2:
                raise ValueError('CG multiplier shape')
            i,q=pair
            if type(i)is not int or type(q)is not int or not 0<=i<len(original)or i in seen:
                raise ValueError('CG original row index/type')
            if not first_eq<=i<last_eq and q<0:
                raise ValueError('CG inequality multiplier sign')
            seen.add(i)
            entries,b=original[i];rhs+=q*b
            for v,a in entries:coeff[v]+=q*a
        # Python // implements floor also for negative coefficients.
        constructed.append(([(v,a//D)for v,a in sorted(coeff.items())if a//D],rhs//D))
        original.append(constructed[-1])
    return rows+[( [(j,1)],u)for j,u in enumerate(upper)]+constructed,upper,columns


def verify(path,H,witness,certificate):
    raw=parse_mm(Path(path));check_witness(raw,witness,H)
    if certificate.get('row_family')!='precedence_energy_CG_v1':
        raise ValueError('certificate family')
    rows,upper,columns=cut_rows(raw,H,certificate['CG_cuts'])
    D=certificate.get('denominator');ys=certificate.get('inequality_dual_integers');zs=certificate.get('equality_dual_integers')
    if type(D)is not int or D<=0 or len(ys)!=len(rows)or len(zs)!=raw['n']:
        raise ValueError('dual dimensions')
    if any(type(y)is not int or y>0 for y in ys)or any(type(z)is not int for z in zs):
        raise ValueError('dual multiplier sign/type')
    # Every new row must retain the independently checked feasible witness.
    selected=[]
    for j,mid in enumerate(witness['mode_ids'],1):
        selected.append(next(k for k,m in enumerate(raw['modes'][j])if m[0]==mid))
    point=witness['starts']+[int(k==selected[j-1])for j in range(1,raw['n']+1)for k in range(len(raw['modes'][j]))]
    for entries,b in rows:
        if sum(a*point[v]for v,a in entries)>b:
            raise ValueError('CG row rejects original feasible witness')
    residual=[0]*len(upper);residual[raw['n']-1]=D;numerator=0
    for (entries,b),y in zip(rows,ys):
        numerator+=b*y
        for v,a in entries:residual[v]-=a*y
    for j,z in enumerate(zs,1):
        numerator+=z
        for k in range(len(raw['modes'][j])):residual[columns[j,k]]-=z
    numerator+=sum(min(0,r)*u for r,u in zip(residual,upper))
    if type(certificate.get('claimed_numerator'))is not int or numerator!=certificate['claimed_numerator']:
        raise ValueError('exact dual numerator mismatch')
    lb=(numerator+D-1)//D
    if lb>H:raise ValueError('lower bound exceeds feasible witness')
    return {'integer_makespan_lb':lb,'numerator':numerator,'denominator':D,
            'CG_cuts':len(certificate['CG_cuts']),'inequalities':len(rows),
            'input_sha256':hashlib.sha256(Path(path).read_bytes()).hexdigest()}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('directory',type=Path);args=ap.parse_args();out=args.directory
    start=time.monotonic();claim=json.loads((out/'claim.json').read_text());certificate=json.loads((out/'certificate.json').read_text());witness=json.loads((out/'witness.json').read_text())
    path=Path('data/mmlib/plus')/claim['instance'];H=claim['H'];got=verify(path,H,witness,certificate)
    if got['integer_makespan_lb']!=claim['new_LB']or got['input_sha256']!=claim['input_sha256']:
        raise ValueError('claim/source mismatch')
    negatives=[]
    def reject(label,c,w=witness):
        try:verify(path,H,w,c)
        except(ValueError,TypeError,KeyError):negatives.append(label)
        else:raise AssertionError('corrupted control accepted: '+label)
    bad=copy.deepcopy(certificate);bad['claimed_numerator']+=1;reject('numerator',bad)
    bad=copy.deepcopy(certificate);bad['inequality_dual_integers'][0]=1;reject('dual_sign',bad)
    if certificate['CG_cuts']:
        bad=copy.deepcopy(certificate);bad['CG_cuts'][0]['denominator']=0;reject('CG_denominator',bad)
        bad=copy.deepcopy(certificate);bad['CG_cuts'][0]['original_row_multipliers'].append([0,-1]);reject('CG_sign',bad)
        bad=copy.deepcopy(certificate);bad['CG_cuts'][0]['original_row_multipliers'].append([999999,1]);reject('CG_source_row',bad)
    badw=copy.deepcopy(witness);badw['mode_ids'][0]=99999;reject('witness',certificate,badw)
    URL='http://solutionsupdate.ugent.be/sites/default/files/datasets/MMplus_2.csv'
    data=urlopen(Request(URL,headers={'User-Agent':'shutdown-schedule-worker/020'}),timeout=30).read();(out/'MMplus_2.current.csv').write_bytes(data)
    lines=data.decode('latin1').splitlines();begin=next(i for i,line in enumerate(lines)if line.startswith('ID;'))
    live={r['Ref1']:r for r in csv.DictReader(lines[begin:],delimiter=';')if r.get('Ref1')};row=live[claim['instance']]
    lb,ub=int(row['LB value']),int(row['UB value'])
    if not lb<got['integer_makespan_lb']<=ub:raise ValueError('fresh strict live gate failed')
    evidence={'checked':got,'previous_LB':claim['previous_LB'],'extra_units':got['integer_makespan_lb']-claim['previous_LB'],
              'live_url':URL,'live_sha256':hashlib.sha256(data).hexdigest(),'live_LB':lb,'live_UB':ub,
              'negative_controls_rejected':negatives,'seconds':time.monotonic()-start,
              'evidence':'independently checked exact CG/dual replay; not submitted or accepted'}
    (out/'verification.json').write_text(json.dumps(evidence,indent=2)+'\n');print(json.dumps(evidence,indent=2))


if __name__=='__main__':main()
