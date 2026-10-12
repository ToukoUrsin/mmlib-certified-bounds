"""Standard-library raw-input checker for conservative renewable scales.

The parser, base-row reconstruction and witness sweep are adapted from the
previous worker's independent tree checker. New scale validity is checked
without trusting transform generators: a capacity-bounded unbounded knapsack
DP proves the maximum weight of ANY demand multiset at an instant. Every
LP coefficient is then rebuilt with Python integer arithmetic.
"""
from __future__ import annotations
import argparse, copy, csv, hashlib, json, re, time
from collections import defaultdict
from pathlib import Path
from urllib.request import Request, urlopen

HERE=Path(__file__).resolve().parent
URL='http://solutionsupdate.ugent.be/sites/default/files/datasets/MMplus_2.csv'
def header(pattern: str, text: str) -> int:
    m = re.search(pattern, text)
    if not m:
        raise ValueError(f"missing header: {pattern}")
    return int(m.group(1))


def parse_mm(path: Path):
    text = path.read_text(encoding="utf-8")
    n = header(r"jobs\s*\(.*?\):\s*(\d+)", text)
    nr = header(r"- renewable\s*:\s*(\d+)", text)
    nn = header(r"- nonrenewable\s*:\s*(\d+)", text)
    if header(r"- doubly constrained\s*:\s*(\d+)", text) != 0:
        raise ValueError("doubly-constrained resource family")

    prec = text.split("PRECEDENCE RELATIONS:", 1)[1].split(
        "REQUESTS/DURATIONS", 1
    )[0]
    succ = {}
    counts = {}
    for line in prec.splitlines():
        if not re.match(r"^\s*\d", line):
            continue
        vals = list(map(int, line.split()))
        j, count, declared, *targets = vals
        if j in succ or len(targets) != declared:
            raise ValueError("bad precedence row")
        succ[j] = tuple(targets)
        counts[j] = count
    if set(succ) != set(range(1, n + 1)):
        raise ValueError("precedence rows do not cover all jobs")

    modes = {j: [] for j in range(1, n + 1)}
    current = None
    width = nr + nn + 2
    mode_text = text.split("REQUESTS/DURATIONS", 1)[1].split(
        "RESOURCE AVAILABILITIES", 1
    )[0]
    for line in mode_text.splitlines():
        if not re.match(r"^\s*\d", line):
            continue
        vals = list(map(int, line.split()))
        if len(vals) == width + 1:
            current = vals.pop(0)
        if current is None or len(vals) != width:
            raise ValueError("bad mode row")
        mid, duration, *quantities = vals
        modes[current].append((mid, duration, tuple(quantities)))
    for j in range(1, n + 1):
        if len(modes[j]) != counts[j] or len({m[0] for m in modes[j]}) != counts[j]:
            raise ValueError(f"mode mismatch at job {j}")

    caps = [
        list(map(int, line.split()))
        for line in text.split("RESOURCE AVAILABILITIES", 1)[1].splitlines()
        if re.match(r"^\s*\d", line)
    ]
    if len(caps) != 1 or len(caps[0]) != nr + nn:
        raise ValueError("bad capacity row")
    return {"n": n, "nr": nr, "nn": nn, "succ": succ, "modes": modes,
            "caps": tuple(caps[0]), "path": str(path)}


def closure(succ, n):
    descendants = {j: set() for j in range(1, n + 1)}
    for j in range(1, n + 1):
        todo = list(succ[j])
        while todo:
            k = todo.pop()
            if k in descendants[j]:
                continue
            descendants[j].add(k)
            todo.extend(succ[k])
    ancestors = {j: {i for i in range(1, n + 1) if j in descendants[i]}
                 for j in range(1, n + 1)}
    return ancestors, descendants


def build_rows(raw, horizon, conditional=None):
    """Rebuild the exact row order used by ``precedence_energy_v1``."""
    n, nr, nn = raw["n"], raw["nr"], raw["nn"]
    modes, succ, caps = raw["modes"], raw["succ"], raw["caps"]
    x = {}
    upper = [horizon] * n
    upper[0] = 0
    for j in range(1, n + 1):
        for k in range(len(modes[j])):
            x[j, k] = len(upper)
            upper.append(1)
    if conditional is not None:
        if len(conditional) != n:
            raise ValueError("conditional domain dimension")
        for j, allowed in enumerate(conditional, 1):
            ids = {m[0] for m in modes[j]}
            if not allowed or len(allowed) != len(set(allowed)) or not set(allowed) <= ids:
                raise ValueError("invalid conditional domain")
            for k, (mid, _d, _q) in enumerate(modes[j]):
                if mid not in allowed:
                    upper[x[j, k]] = 0

    rows = []
    def add(items, rhs=0):
        coeff = defaultdict(int)
        for var, value in items:
            coeff[var] += value
        rows.append(([(v, a) for v, a in coeff.items() if a], rhs))

    for j in range(1, n + 1):
        duration = [(x[j, k], m[1]) for k, m in enumerate(modes[j])]
        for target in succ[j]:
            add([(j - 1, 1), (target - 1, -1), *duration])
        add([(j - 1, 1), (n - 1, -1), *duration])
    for r in range(nn):
        add([(x[j, k], m[2][nr + r])
             for j in range(1, n + 1) for k, m in enumerate(modes[j])], caps[nr + r])
    for r in range(nr):
        add([(x[j, k], m[1] * m[2][r])
             for j in range(1, n + 1) for k, m in enumerate(modes[j])]
            + [(n - 1, -caps[r])])

    ancestors, descendants = closure(succ, n)
    for j in range(2, n):
        for r in range(nr):
            cap = caps[r]
            if ancestors[j]:
                add([(x[a, k], m[1] * m[2][r])
                     for a in sorted(ancestors[j])
                     for k, m in enumerate(modes[a])] + [(j - 1, -cap)])
            if descendants[j]:
                add([(x[a, k], m[1] * m[2][r])
                     for a in sorted(descendants[j])
                     for k, m in enumerate(modes[a])]
                    + [(j - 1, cap), (n - 1, -cap)]
                    + [(x[j, k], cap * m[1])
                       for k, m in enumerate(modes[j])])
    return rows, upper, x


def replay_certificate(raw, horizon, witness, cert, conditional):
    rows, upper, x = build_rows(raw, horizon, conditional)
    n, modes = raw["n"], raw["modes"]
    if cert.get("row_family") != "precedence_energy_v1":
        raise ValueError("certificate family")
    D = cert.get("denominator")
    ys, zs = cert.get("inequality_dual_integers"), cert.get("equality_dual_integers")
    if type(D) is not int or D <= 0 or len(ys) != len(rows) or len(zs) != n:
        raise ValueError("certificate dimensions")
    if any(type(y) is not int or y > 0 for y in ys) or any(type(z) is not int for z in zs):
        raise ValueError("certificate sign/type")
    residual = [0] * len(upper)
    residual[n - 1] = D
    numerator = 0
    for (entries, rhs), y in zip(rows, ys):
        numerator += rhs * y
        for var, value in entries:
            residual[var] -= value * y
    for j, z in enumerate(zs, 1):
        numerator += z
        for k in range(len(modes[j])):
            residual[x[j, k]] -= z
    numerator += sum(min(0, r) * u for r, u in zip(residual, upper))
    if cert.get("claimed_numerator") != numerator:
        raise ValueError("certificate numerator mismatch")
    return (numerator + D - 1) // D


def check_witness(raw, witness, horizon):
    n, nr, nn = raw["n"], raw["nr"], raw["nn"]
    starts, mids = witness["starts"], witness["mode_ids"]
    if len(starts) != n or len(mids) != n or any(type(t) is not int or t < 0 for t in starts):
        raise ValueError("witness shape")
    selected = []
    for j, mid in enumerate(mids, 1):
        choices = {m[0]: m for m in raw["modes"][j]}
        if type(mid) is not int or mid not in choices:
            raise ValueError("invalid witness mode")
        selected.append(choices[mid])
    ends = [s + m[1] for s, m in zip(starts, selected)]
    if starts[0] != 0 or starts[-1] != max(ends) or starts[-1] != horizon:
        raise ValueError("witness horizon")
    for j in range(1, n + 1):
        if any(ends[j - 1] > starts[t - 1] for t in raw["succ"][j]):
            raise ValueError("witness precedence")
    for r in range(nn):
        if sum(m[2][nr + r] for m in selected) > raw["caps"][nr + r]:
            raise ValueError("witness nonrenewable capacity")
    for t in range(horizon):
        for r in range(nr):
            if sum(m[2][r] for s, e, m in zip(starts, ends, selected) if s <= t < e) > raw["caps"][r]:
                raise ValueError("witness renewable capacity")


def scale_rows(raw, horizon, scales, conditional=None):
    rows, upper, x = build_rows(raw, horizon,conditional)
    n=raw['n']; modes=raw['modes']
    ancestors, descendants=closure(raw['succ'],n)
    def add(items):
        coefficients=defaultdict(int)
        for var,value in items: coefficients[var]+=value
        rows.append(([(v,a) for v,a in coefficients.items() if a],0))
    for tr in scales:
        r=tr.get('resource'); T=tr.get('transformed_capacity')
        if type(r)is not int or not 0<=r<raw['nr'] or type(T)is not int or T<=0:
            raise ValueError('invalid transformed capacity/resource')
        C=raw['caps'][r]
        if tr.get('capacity')!=C: raise ValueError('source capacity mismatch')
        demands=sorted({m[2][r] for ms in modes.values() for m in ms})
        weights=tr.get('weights')
        if tr.get('demands')!=demands or not isinstance(weights,list) or len(weights)!=len(demands):
            raise ValueError('transform demand schema mismatch')
        if any(type(w)is not int or w<0 for w in weights): raise ValueError('invalid demand weight')
        if any(q<0 or q>C for q in demands): raise ValueError('original demand unsupported')
        if 0 in demands and weights[demands.index(0)]!=0: raise ValueError('zero-demand nonzero weight')
        # Unbounded knapsack allows repeated jobs and modes, a safe superset
        # of every instantaneous feasible schedule configuration.
        dp=[0]*(C+1)
        for c in range(1,C+1):
            dp[c]=max(dp[c-1],max([dp[c-q]+w for q,w in zip(demands,weights) if 0<q<=c]+[0]))
        if dp[C]>T: raise ValueError('resource transform excludes feasible configuration')
        weights=dict(zip(demands,weights))
        def energy(jobs):
            return [(x[j,k],m[1]*weights[m[2][r]]) for j in jobs for k,m in enumerate(modes[j])]
        add(energy(range(1,n+1))+[(n-1,-T)])
        for j in range(2,n):
            if ancestors[j]: add(energy(sorted(ancestors[j]))+[(j-1,-T)])
            if descendants[j]:
                add(energy(sorted(descendants[j]))+[(j-1,T),(n-1,-T)]+
                    [(x[j,k],T*m[1]) for k,m in enumerate(modes[j])])
    return rows,upper,x


def verify(raw, scope, cert,conditional=None):
    H=scope['H']
    if type(H)is not int or H<0: raise ValueError('horizon type')
    check_witness(raw,scope['witness'],H)
    if cert.get('row_family')!='renewable_rounding_v1': raise ValueError('certificate family')
    rows,upper,x=scale_rows(raw,H,cert['transforms'],conditional)
    D=cert['denominator']; ys=cert['inequality_dual_integers']; zs=cert['equality_dual_integers']
    if type(D)is not int or D<=0 or len(ys)!=len(rows) or len(zs)!=raw['n']:
        raise ValueError('certificate dimensions')
    if any(type(y)is not int or y>0 for y in ys) or any(type(z)is not int for z in zs):
        raise ValueError('certificate sign/types')
    residual=[0]*len(upper); residual[raw['n']-1]=D
    numerator=0
    for (entries,b),y in zip(rows,ys):
        numerator+=b*y
        if y:
            for v,a in entries: residual[v]-=a*y
    for j,z in enumerate(zs,1):
        numerator+=z
        for k in range(len(raw['modes'][j])): residual[x[j,k]]-=z
    correction=sum(min(0,r)*u for r,u in zip(residual,upper))
    numerator+=correction
    if cert.get('claimed_numerator')!=numerator: raise ValueError('exact numerator mismatch')
    lower=(numerator+D-1)//D
    if lower>H or lower!=scope['lb']: raise ValueError('lower-bound claim mismatch')
    return {'lb':lower,'numerator':numerator,'box_correction':correction,
            'scale_count':len(cert['transforms']),'inequalities':len(rows)}


def rejected(fn):
    try:fn()
    except (ValueError,AssertionError,KeyError,TypeError):return True
    raise AssertionError('negative control accepted')


def verify_tree(raw,scope,tree):
    original=[[m[0] for m in raw['modes'][j]] for j in range(1,raw['n']+1)]
    counts={'leaves':0,'splits':0}
    def visit(node,domains):
        if set(node)=={'leaf_certificate'}:
            counts['leaves']+=1;cert=node['leaf_certificate'];D=cert['denominator']
            leafscope={**scope,'lb':(cert['claimed_numerator']+D-1)//D}
            return verify(raw,leafscope,cert,domains)['lb']
        if set(node)!={'job_id','mode_id','included','excluded'}:raise ValueError('tree schema')
        j,mid=node['job_id'],node['mode_id']
        if type(j)is not int or type(mid)is not int or not 1<=j<=raw['n']:
            raise ValueError('tree source index')
        if mid not in domains[j-1] or len(domains[j-1])<2:raise ValueError('invalid source partition')
        counts['splits']+=1
        included=[d[:] for d in domains];excluded=[d[:] for d in domains]
        included[j-1]=[mid];excluded[j-1]=[m for m in excluded[j-1] if m!=mid]
        return min(visit(node['included'],included),visit(node['excluded'],excluded))
    lb=visit(tree['root'],original)
    if lb!=tree['claimed_lb'] or lb>scope['H']:raise ValueError('global covered bound mismatch')
    return {'lb':lb,**counts}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,default=HERE/'pilot-002')
    args=ap.parse_args();begin=time.monotonic()
    payload=urlopen(Request(URL,headers={'User-Agent':'Mozilla/5.0'}),timeout=60).read()
    (args.out/'MMplus_2.current.csv').write_bytes(payload)
    lines=payload.decode('latin1').replace('\\r\\n','\n').splitlines()
    header=next(i for i,line in enumerate(lines) if line.startswith('ID;'))
    live={r['Ref1']:r for r in csv.DictReader(lines[header:],delimiter=';')}
    checked=[]
    for path in sorted(args.out.glob('*/certificate.json')):
        scope=json.loads((path.parent/'scope.json').read_text());cert=json.loads(path.read_text())
        source=path.parent/'input.mm';hashval=hashlib.sha256(source.read_bytes()).hexdigest()
        if hashval!=scope['input_sha256']:raise ValueError('input hash mismatch')
        raw=parse_mm(source);result=verify(raw,scope,cert)
        row=live[scope['instance']];LB=int(row['LB value']);UB=int(row['UB value'])
        if not LB<result['lb']<=UB:raise ValueError('current table gate failed')
        controls=[]
        bad=copy.deepcopy(cert);bad['claimed_numerator']+=1
        rejected(lambda:verify(raw,scope,bad));controls.append('wrong_numerator')
        bad=copy.deepcopy(cert);bad['inequality_dual_integers'][0]=1
        rejected(lambda:verify(raw,scope,bad));controls.append('positive_dual')
        bad=copy.deepcopy(cert);bad['transforms'][0]['weights'][0]=bad['transforms'][0]['transformed_capacity']+1
        rejected(lambda:verify(raw,scope,bad));controls.append('invalid_resource_scale')
        badscope=copy.deepcopy(scope);badscope['witness']['mode_ids'][1]=-1
        rejected(lambda:verify(raw,badscope,cert));controls.append('invalid_witness')
        badscope=copy.deepcopy(scope);badscope['lb']+=1
        rejected(lambda:verify(raw,badscope,cert));controls.append('wrong_integer_claim')
        e={'instance':scope['instance'],**result,'live_lb':LB,'live_ub':UB,
           'previous_lb':scope['previous_lb'],'input_sha256':hashval,'negative_controls':controls}
        checked.append(e);print(json.dumps(e),flush=True)
    report={'source_url':URL,'live_sha256':hashlib.sha256(payload).hexdigest(),
            'checked':len(checked),'negative_controls_rejected':sum(len(e['negative_controls']) for e in checked),
            'extra_units':sum(e['lb']-max(e['previous_lb'],e['live_lb']) for e in checked),
            'delta_vs_live':sum(e['lb']-e['live_lb'] for e in checked),
            'rows':checked,'seconds':time.monotonic()-begin,
            'evidence_level':'reported and independently checked; not submitted or accepted'}
    (args.out/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='rows'}),flush=True)


if __name__=='__main__':main()
