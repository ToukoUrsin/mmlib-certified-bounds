"""Cold certificate replay from original raw input, using Python integer arithmetic.
No numpy, scipy, construction parser, or solver imports. Global proof splits at
known feasible H: schedules > H satisfy any admitted bound <= H; schedules <= H
embed in the original-mode indicator and activity-start relaxation below.
"""
import hashlib,json,re
from pathlib import Path
from check_multi_mode import check

def verify(path,H,witness,cert,*,conditional_domains=None):
    raw=Path(path).read_text();n=int(re.search(r'jobs\s*\(.*\):\s*(\d+)',raw)[1]);nr=int(re.search(r'- renewable\s*:\s*(\d+)',raw)[1]);nn=int(re.search(r'- nonrenewable\s*:\s*(\d+)',raw)[1]);assert int(re.search(r'- doubly constrained\s*:\s*(\d+)',raw)[1])==0
    ch=check(path,witness['starts'],witness['mode_ids'],claimed=20*H)
    if not ch['feasible']:raise ValueError('H needs an original-input feasible witness')
    counts={};succ={}
    for line in raw.split('PRECEDENCE RELATIONS:')[1].split('REQUESTS/DURATIONS')[0].splitlines():
        if re.match(r'^\s*\d',line):
            j,c,k,*ss=map(int,line.split())
            if j in counts or len(ss)!=k:raise ValueError('Invalid original precedence')
            counts[j]=c;succ[j]=ss
    modes={j:[] for j in range(1,n+1)};current=None
    for line in raw.split('REQUESTS/DURATIONS')[1].split('RESOURCE AVAILABILITIES')[0].splitlines():
        if not re.match(r'^\s*\d',line):continue
        v=list(map(int,line.split()))
        if len(v)==nr+nn+3:current=v.pop(0)
        if current is None or len(v)!=nr+nn+2:raise ValueError('Invalid raw mode')
        mid,d,*qs=v;modes[current].append((mid,d,qs))
    for j in modes:
        if len(modes[j])!=counts[j] or len({m[0] for m in modes[j]})!=counts[j]:raise ValueError('Missing original modes')
    caprows=[list(map(int,l.split())) for l in raw.split('RESOURCE AVAILABILITIES')[1].splitlines() if re.match(r'^\s*\d',l)]
    if len(caprows)!=1 or len(caprows[0])!=nr+nn:raise ValueError('Invalid original capacities')
    caps=caprows[0];xs={};upper=[H]*n;upper[0]=0
    for j in range(1,n+1):
        for k,_ in enumerate(modes[j]):xs[j,k]=len(upper);upper.append(1)
    if conditional_domains is not None:
        if len(conditional_domains)!=n:raise ValueError('Conditional domain dimensions')
        for j,allowed in enumerate(conditional_domains,1):
            if not allowed or len(set(allowed))!=len(allowed) or any(type(mid)is not int or mid not in {m[0] for m in modes[j]} for mid in allowed):raise ValueError('Invalid conditional original mode domain')
            for k,(mid,d,qs) in enumerate(modes[j]):
                if mid not in allowed:upper[xs[j,k]]=0
    rows=[]
    for j in range(1,n+1):
        dur=[(xs[j,k],d) for k,(_,d,qs) in enumerate(modes[j])]
        for s in succ[j]:rows.append(([(j-1,1),(s-1,-1)]+dur,0))
        rows.append(([(j-1,1),(n-1,-1)]+dur,0))
    for r in range(nn):rows.append(([(xs[j,k],qs[nr+r]) for j in range(1,n+1) for k,(_,d,qs) in enumerate(modes[j])],caps[nr+r]))
    for r in range(nr):rows.append(([(xs[j,k],d*qs[r]) for j in range(1,n+1) for k,(_,d,qs) in enumerate(modes[j])]+[(n-1,-caps[r])],0))
    family=cert.get('row_family','base')
    if family not in ('base','precedence_energy_v1'):raise ValueError('Unknown certificate row family')
    if family=='precedence_energy_v1':
        # Independent graph traversal on separately parsed ORIGINAL links.
        followers={j:set() for j in modes}
        for j in modes:
            pending=list(succ[j])
            while pending:
                a=pending.pop()
                if a in followers[j]:continue
                followers[j].add(a);pending.extend(succ[a])
        prior={j:{a for a in modes if j in followers[a]} for j in modes}
        for j in range(2,n):
            for r in range(nr):
                c=caps[r]
                if prior[j]:
                    rows.append(([(xs[a,k],d*qs[r]) for a in sorted(prior[j]) for k,(_,d,qs) in enumerate(modes[a])]+[(j-1,-c)],0))
                if followers[j]:
                    rows.append(([(xs[a,k],d*qs[r]) for a in sorted(followers[j]) for k,(_,d,qs) in enumerate(modes[a])]+[(j-1,c),(n-1,-c)]+[(xs[j,k],c*d) for k,(_,d,qs) in enumerate(modes[j])],0))
    D=cert['denominator'];ys=cert['inequality_dual_integers'];zs=cert['equality_dual_integers']
    if type(D)is not int or D<=0 or len(ys)!=len(rows) or len(zs)!=n:raise ValueError('Invalid certificate dimensions')
    if any(type(y)is not int or y>0 for y in ys) or any(type(z)is not int for z in zs):raise ValueError('Invalid multiplier sign/type')
    residual=[0]*len(upper);residual[n-1]=D;numerator=0
    for (entries,b),y in zip(rows,ys):
        numerator+=b*y
        for v,a in entries:residual[v]-=a*y
    for j,z in enumerate(zs,1):
        numerator+=z
        for k in range(len(modes[j])):residual[xs[j,k]]-=z
    correction=sum(min(0,r)*u for r,u in zip(residual,upper));numerator+=correction
    if numerator!=cert['claimed_numerator']:raise ValueError('Exact numerator differs')
    lower=(numerator+D-1)//D
    if conditional_domains is None and lower>H:raise ValueError('Certified bound exceeds witness')
    return {'numerator':numerator,'denominator':D,'integer_makespan_lb':lower,'box_correction_numerator':correction,'variables':len(upper),'inequalities':len(rows),'conditional':conditional_domains is not None,'input_sha256':hashlib.sha256(Path(path).read_bytes()).hexdigest()}

def main(root=Path('results/026-modal-lp-screen')):
    live=json.loads(Path('results/023-multimode-records/live_comparators.json').read_text());lookup={r['instance']:r for r in live['selected']};out=[]
    for row in json.loads((root/'bounds.json').read_text()):
        name=row['instance'];path=Path('data/mmlib')/name;cert=json.loads((root/(Path(name).stem+'_certificate.json')).read_text());witness=lookup[name];exact=verify(path,row['liveUB'],witness,cert)
        assert exact['integer_makespan_lb']==row['exact']['integer_charged_lb'] and exact['numerator']==row['exact']['numerator']
        for bad in ({**cert,'claimed_numerator':cert['claimed_numerator']+1},{**cert,'inequality_dual_integers':[1]+cert['inequality_dual_integers'][1:]}):
            try:verify(path,row['liveUB'],witness,bad)
            except ValueError:pass
            else:raise AssertionError('Invalid certificate accepted')
        badw={**witness,'mode_ids':[99999]+witness['mode_ids'][1:]}
        try:verify(path,row['liveUB'],badw,cert)
        except ValueError:pass
        else:raise AssertionError('Invalid horizon witness accepted')
        out.append({'instance':name,'exact':exact,'live_LB':row['liveLB'],'improvement':exact['integer_makespan_lb']-row['liveLB'],'negative_certificate_controls_rejected':2,'invalid_horizon_witness_rejected':True})
    (root/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print('Independent integer replay',len(out),'certificates;20badcertificates/10badwitnessesrejected');print([(r['instance'],r['live_LB'],r['exact']['integer_makespan_lb']) for r in out if r['improvement']>0])
if __name__=='__main__':main()
