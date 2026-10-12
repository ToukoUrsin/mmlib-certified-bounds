"""Independent exact certificate checker. Standard library; safe under python -O.
Parses original rows independently of the packet's parser and constructor.
"""
import argparse, gzip, hashlib, itertools, json, re, time
from pathlib import Path
from prefix_essential import require, check_frontiers
ROOT=Path(__file__).resolve().parent
PIN='dcb796d7c15299e01a5019756d396dcb165330d89ba4f87024118b962ef7c27f'


def encoded(x):
    return json.dumps(json.loads(json.dumps(x)),sort_keys=True,separators=(',',':')).encode()


def digest(x):
    return hashlib.sha256(encoded(x)).hexdigest()


def parse(path):
    text=Path(path).read_text()
    require(int(re.search(r'jobs.*?:\s*(\d+)',text).group(1))==52,'job count')
    for name,num in [('renewable',2),('nonrenewable',4),('doubly constrained',0)]:
        require(int(re.search(r'- '+name+r'\s*:\s*(\d+)',text).group(1))==num,'resource declaration')
    succ={}; nm={}; modes={j:{} for j in range(1,53)}
    for line in text.split('PRECEDENCE RELATIONS:')[1].split('REQUESTS/DURATIONS')[0].splitlines():
        if not re.match(r'^\s*\d',line):continue
        a=list(map(int,line.split()));j,n,ns=a[:3]
        require(j not in succ and j in modes,'duplicate/unknown job')
        require(len(a[3:])==ns and len(set(a[3:]))==ns,'successor count/duplicates')
        require(all(j<k<=52 for k in a[3:]),'acyclic original precedence')
        succ[j]=a[3:];nm[j]=n
    job=None
    for line in text.split('REQUESTS/DURATIONS')[1].split('RESOURCE AVAILABILITIES')[0].splitlines():
        if not re.match(r'^\s*\d',line):continue
        a=list(map(int,line.split()))
        if len(a)==9:job=a.pop(0)
        require(job in modes and len(a)==8,'mode row')
        m,d,*q=a
        require(m not in modes[job],'duplicate mode')
        require(d>=0 and len(q)==6 and min(q)>=0,'mode quantities')
        modes[job][m]=(d,tuple(q))
    caprows=[list(map(int,line.split())) for line in text.split('RESOURCE AVAILABILITIES')[1].splitlines() if re.match(r'^\s*\d',line)]
    require(caprows==[[28,29,282,297,271,301]],'all original capacities')
    require(set(succ)==set(modes),'all original jobs')
    for j in modes:
        require(nm[j]==len(modes[j]),'declared number of modes')
        require(set(modes[j])==({1} if j in (1,52) else {1,2,3}),'original mode IDs')
        for d,q in modes[j].values():
            require((d==0 and not any(q)) if j in (1,52) else (d>0 and q[1]>0),'dummy/positive demand condition')
    # Every real job must be inside the source-sink project, checked explicitly.
    reached={1}
    for j in range(1,53):
        if j in reached:reached.update(succ[j])
    require(len(reached)==52 and succ[52]==[],'source reachability')
    sink={52}
    for j in reversed(range(1,53)):
        if any(k in sink for k in succ[j]):sink.add(j)
    require(len(sink)==52,'sink reachability')
    return succ,modes,caprows[0]


def coverage(modes,caps):
    costs={};minimum={};allowed={}
    for j in sorted(modes):
        row={}
        for m,(d,q) in modes[j].items():row[m]=5*d*q[1]+5*q[2]+9*q[5]
        costs[j]=row;minimum[j]=min(row.values())
    base=sum(minimum.values());gap=5*(32*caps[1])+5*caps[2]+9*caps[5]-base
    require((base,gap)==(8755,4),'separator arithmetic')
    for j in sorted(modes):allowed[j]=[m for m in sorted(modes[j]) if costs[j][m]-minimum[j]<=gap]
    limits=[32*caps[0],32*caps[1]]+caps[2:]
    records=[];surviving=[]
    # Different accumulation than constructor; all 64 combinations are retained.
    for vector in itertools.product(*(allowed[j] for j in sorted(allowed))):
        usage=[0]*6;excess=0
        for j,m in enumerate(vector,1):
            d,q=modes[j][m];excess+=costs[j][m]-minimum[j]
            for r in range(6):usage[r]+=(d if r<2 else 1)*q[r]
        violated=[r for r in range(6) if usage[r]>limits[r]]
        records.append({'mode_ids':list(vector),'excess':excess,'usage':usage,
                        'violated_rows':violated,'cost_excluded':excess>gap})
        if excess<=gap and not violated:surviving.append({'mode_ids':list(vector),'usage':usage})
    require(len(surviving)==2 and all(v['usage'][1]==928 for v in surviving),'saturated mode coverage')
    return {'base':base,'gap':gap,'costs':costs,'minimum_costs':minimum,
            'domains':allowed,'limits':limits,'combinations':records,'survivors':surviving}


def check_witness(witness,succ,modes,caps):
    require(set(witness)=={'mode_ids','starts'},'witness fields')
    mids,starts=witness['mode_ids'],witness['starts']
    require(len(mids)==52 and len(starts)==52,'witness shape')
    require(all(type(x) is int and x>=0 for x in starts),'witness starts')
    require(all(type(m) is int and m in modes[j] for j,m in enumerate(mids,1)),'witness modes')
    selected=[modes[j][m] for j,m in enumerate(mids,1)]
    ends=[s+d for s,(d,q) in zip(starts,selected)]
    require(starts[0]==0 and starts[-1]==33 and max(ends)==33,'witness H33')
    require(all(ends[j-1]<=starts[k-1] for j in succ for k in succ[j]),'witness precedence')
    nr=[sum(q[r] for d,q in selected) for r in range(2,6)]
    require(all(x<=y for x,y in zip(nr,caps[2:])),'witness nonrenewable')
    profiles=[[sum(q[r] for s,e,(d,q) in zip(starts,ends,selected) if s<=t<e)
               for r in range(2)] for t in range(33)]
    require(all(row[r]<=caps[r] for row in profiles for r in range(2)),'witness renewable')
    return {'nr_usage':nr,'resource_profiles':profiles,'horizon':33}


def check_boundary(boundary,succ,modes,domains,caps):
    require(set(boundary)=={'schema','length','idle_R1','scheduled'},'boundary fields')
    require(boundary['schema']=='original_mode_partial_prefix_v1' and boundary['length']==16 and boundary['idle_R1']==15,'boundary scope')
    schedule={}
    for row in boundary['scheduled']:
        require(set(row)=={'job','mode','start'},'boundary row')
        j,m,s=row['job'],row['mode'],row['start']
        require(type(j) is int and j in domains and j not in schedule,'boundary job')
        require(type(m) is int and m in domains[j],'boundary original mode')
        require(type(s) is int and 0<=s<16,'boundary start')
        schedule[j]=(m,s)
    for j,(m,s) in schedule.items():
        require(s+modes[j][m][0]<=32,'boundary deadline')
        for i,ks in succ.items():
            if j in ks and i!=1:
                require(i in schedule,'boundary missing predecessor')
                mi,si=schedule[i]
                require(si+modes[i][mi][0]<=s,'boundary precedence')
    profile=[]
    for t in range(16):
        q=[0,0]
        for j,(m,s) in schedule.items():
            d,r=modes[j][m]
            if s<=t<s+d:
                q[0]+=r[0];q[1]+=r[1]
        require(q[0]<=caps[0] and q[1]==caps[1],'boundary cumulative condition')
        profile.append(q)
    require(sum(caps[0]-q[0] for q in profile)==15,'boundary idle')
    return {'jobs_started':len(schedule),'idle_R1':15,'length':16,'profiles':profile,
            'is_complete_schedule':False}


def verify(bundle, input_path=None, certificate=None, horizon_witness=None):
    started=time.perf_counter();bundle=Path(bundle)
    path=Path(input_path) if input_path else ROOT/'data/mmlib/plus/Jall30_5.mm'
    require(hashlib.sha256(path.read_bytes()).hexdigest()==PIN,'pinned original bytes')
    cert=certificate if certificate is not None else json.loads((bundle/'certificate.json').read_text())
    require(cert.get('input_sha256')==PIN,'certificate input hash')
    succ,modes,caps=parse(path);cov=coverage(modes,caps)
    require(encoded(cov)==encoded(json.loads((bundle/'mode-coverage.json').read_text())),'coverage ledger')
    domains={j:sorted({v['mode_ids'][j-1] for v in cov['survivors']}) for j in range(2,52)}
    pred={j:sum(1<<i for i in domains if j in succ[i]) for j in domains}
    budget=max(32*caps[0]-v['usage'][0] for v in cov['survivors'])
    require(budget==14,'shared idle allowance')
    raw_trace=json.loads(gzip.decompress((bundle/'prefix-trace.json.gz').read_bytes()))
    require(len(raw_trace)==17,'prefix proof depth')
    frontiers=[]
    for t,rows in enumerate(raw_trace):
        F=set()
        for row in rows:
            require(isinstance(row,list) and len(row)==3,'state shape')
            done,active,idle=row
            require(type(done) is int and type(idle) is int and 0<=idle<=budget,'state scalar')
            require(done>=0 and done & ~sum(1<<j for j in domains)==0,'completed job bits')
            seen=set();aa=[]
            for j,m,r in active:
                require(type(j) is int and j in domains and j not in seen and not done&(1<<j),'active job')
                require(type(m) is int and m in domains[j],'active mode')
                require(type(r) is int and 1<=r<modes[j][m][0],'active remaining time')
                aa.append((j,m,r));seen.add(j)
            require(aa==sorted(aa),'active canonical order')
            z=(done,tuple(aa),idle)
            require(z not in F,'duplicate stored state');F.add(z)
        require(rows==[[d,[list(x) for x in a],i] for d,a,i in sorted(F)],'frontier canonical order')
        frontiers.append(F)
    count,ambiguous=check_frontiers(frontiers,modes,domains,pred,caps,32,budget)
    witness=horizon_witness if horizon_witness is not None else json.loads((bundle/'witness-H33.json').read_text())
    wcheck=check_witness(witness,succ,modes,caps)
    boundary=json.loads((bundle/'prefix-boundary.json').read_text())
    bcheck=check_boundary(boundary,succ,modes,domains,caps)
    expected={'schema':'mmlib_exact_shared_prefix_v2','input_sha256':PIN,
              'target':32,'proved_lb':33,'checked_ub':33,
              'weights':[0,5,5,0,0,9],'sum_mode_minima':cov['base'],
              'excess_budget':cov['gap'],'coverage_sha256':digest(cov),
              'survivors':cov['survivors'],'shared_idle_budget':budget,
              'prefix_slots':16,'frontier_counts':[len(F) for F in frontiers],
              'transitions':count,'ambiguous_mode_starts':ambiguous,
              'trace_sha256':digest(raw_trace),'witness_sha256':digest(witness),
              'boundary_sha256':digest(boundary)}
    # Strict schema comparison: no unchecked status, timing, or extra fields.
    require(encoded(cert)==encoded(expected),'certificate field mismatch')
    return {'status':'EXACT_LB33_UB33_VERIFIED','seconds':time.perf_counter()-started,
            'input_sha256':PIN,'original_jobs':52,'real_jobs':50,
            'original_modes':sum(len(x) for x in modes.values()),
            'original_arcs':sum(len(ks) for ks in succ.values()),'capacities':caps,
            'cost_domain_vectors':len(cov['combinations']),
            'cost_admissible_vectors':sum(not r['cost_excluded'] for r in cov['combinations']),
            'mode_survivors':len(cov['survivors']),
            'transitions':count,'frontier_counts':expected['frontier_counts'],
            'stored_nonempty_states':sum(map(len,frontiers)),
            'ambiguous_mode_starts':ambiguous,
            'witness':wcheck,'tight_prefix_control':bcheck,
            'certified_prefix_inequality':'idle_R1([0,16)) >= 15',
            'required_total_idle_at_C32':'<=14','proved_lb':33,'checked_ub':33}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--bundle',default=str(ROOT/'evidence'))
    ap.add_argument('--input');ap.add_argument('--out');a=ap.parse_args()
    out=verify(a.bundle,a.input)
    if a.out:Path(a.out).write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out))
if __name__=='__main__':main()
