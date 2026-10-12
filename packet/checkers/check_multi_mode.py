"""Independent raw MMLIB checker, no construction parser/engine imports."""
import re
from pathlib import Path

def check(path,starts,modes,scenario=None,claimed=None,mode_charge=10):
    text=Path(path).read_text();n=int(re.search(r'jobs\s*\(.*\):\s*(\d+)',text)[1]);nr=int(re.search(r'- renewable\s*:\s*(\d+)',text)[1]);nn=int(re.search(r'- nonrenewable\s*:\s*(\d+)',text)[1])
    if int(re.search(r'- doubly constrained\s*:\s*(\d+)',text)[1]):raise ValueError('Doubly constrained unsupported')
    precedences=text.split('PRECEDENCE RELATIONS:')[1].split('REQUESTS/DURATIONS')[0]
    links=[];counts={}
    for line in precedences.splitlines():
        if not re.match(r'^\s*\d',line):continue
        j,c,k,*ss=map(int,line.split())
        if len(ss)!=k or j in counts:raise ValueError('Invalid raw precedence')
        counts[j]=c;links.extend((j-1,s-1) for s in ss)
    section=text.split('REQUESTS/DURATIONS')[1].split('RESOURCE AVAILABILITIES')[0]
    data={};current=None
    for line in section.splitlines():
        if not re.match(r'^\s*\d',line):continue
        values=list(map(int,line.split()))
        if len(values)==nr+nn+3:current=values.pop(0)
        if current is None or len(values)!=nr+nn+2:raise ValueError('Invalid raw mode')
        ident,d,*qs=values
        if (current,ident) in data:raise ValueError('Duplicate raw mode')
        data[current,ident]=(d,qs)
    for j,c in counts.items():
        if sum(x[0]==j for x in data)!=c:raise ValueError('Missing raw modes')
    caprows=[list(map(int,l.split())) for l in text.split('RESOURCE AVAILABILITIES')[1].splitlines() if re.match(r'^\s*\d',l)]
    if len(caprows)!=1 or len(caprows[0])!=nr+nn:raise ValueError('Invalid raw capacity')
    caps=caprows[0];errors=[]
    if len(starts)!=n or len(modes)!=n or any(type(t) is not int or t<0 for t in starts):return {'feasible':False,'errors':['Invalid schedule vectors']}
    # Public plan mode values are source IDs, not parser-dependent indices.
    selected=[]
    for j,k in enumerate(modes,1):
        if type(k) is not int or (j,k) not in data:return {'feasible':False,'errors':['Invalid original mode ID']}
        selected.append(data[j,k])
    ends=[s+d for s,(d,q) in zip(starts,selected)];finish=max(ends)
    if starts[0]!=0 or starts[-1]!=finish:errors.append('Dummy/source/completion mismatch')
    for a,b in links:
        if ends[a]>starts[b]:errors.append(f'Original FS {a+1}->{b+1}')
    budgets=[sum(q[nr+r] for d,q in selected) for r in range(nn)]
    for r,use in enumerate(budgets):
        if use>caps[nr+r]:errors.append(f'Nonrenewable budget {r+1}: {use}>{caps[nr+r]}')
    cut=0 if scenario is None else scenario['cut'];displacement=0;changes=0
    if scenario:
        for j in range(1,n-1):
            if scenario['baseline'][j]<cut:
                if starts[j]!=scenario['baseline'][j] or modes[j]!=scenario['baseline_mode_ids'][j]:errors.append(f'Frozen job/mode moved {j+1}')
            elif starts[j]<cut:errors.append(f'Unstarted before cut {j+1}')
            displacement+=abs(starts[j]-scenario['baseline'][j]);changes+=modes[j]!=scenario['baseline_mode_ids'][j]
    event=scenario.get('outage') if scenario else None
    if event and (not 0<=event['resource']<nr or not 0<=event['begin']<event['end'] or not 0<event['loss']<=caps[event['resource']]):raise ValueError('Invalid crew outage')
    overloads=[]
    for t in range(max(finish,event['end'] if event else 0)):
        for r in range(nr):
            use=sum(q[r] for j,(d,q) in enumerate(selected) if starts[j]<=t<ends[j])
            available=caps[r]-(event['loss'] if event and r==event['resource'] and event['begin']<=t<event['end'] else 0)
            if use>available:overloads.append({'time':t,'resource':r,'usage':use,'capacity':available})
    if overloads:errors.append('Renewable resource overload')
    objective=20*(finish-cut)+(displacement+mode_charge*changes if scenario else 0)
    if claimed is not None and claimed!=objective:errors.append('Claimed objective differs')
    return {'feasible':not errors,'errors':errors,'resource_overloads':overloads,'makespan':finish,'remaining_duration':finish-cut,'start_displacement':displacement,'mode_changes':changes,'nonrenewable_usage':budgets,'charged_objective':objective}
