"""Independent standard-library-only MMLIB+ source-mode tree replay.

The tree checker parses each original ``.mm`` file, reconstructs the
precedence/energy inequalities, and recomputes every saved rational dual with
integer arithmetic.  It also checks the supplied feasible horizon witness,
the exact source-mode partition at every split, a fresh public live-table
join, and deliberately corrupted controls.  No repository checker or solver
is imported.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ProcessPoolExecutor
from datetime import datetime, timezone

import copy
import csv
import hashlib
import json
import re
import time
from collections import Counter, defaultdict
from pathlib import Path
from urllib.request import Request, urlopen


URL = "http://solutionsupdate.ugent.be/sites/default/files/datasets/MMplus_2.csv"


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


def build_rows(raw, horizon, conditional=None, interval_energy=False):
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
    if interval_energy:
        # Traverse the original graph independently; no constructor imports.
        for i in range(1, n + 1):
            for j in sorted(descendants[i]):
                between = sorted(descendants[i] & ancestors[j])
                if not between:
                    continue
                for r in range(nr):
                    cap = caps[r]
                    add([(i - 1, cap), (j - 1, -cap)]
                        + [(x[i, k], cap * m[1]) for k, m in enumerate(modes[i])]
                        + [(x[g, k], m[1] * m[2][r])
                           for g in between for k, m in enumerate(modes[g])])
    return rows, upper, x


def replay_certificate(raw, horizon, witness, cert, conditional):
    family = cert.get('row_family')
    if family not in ('precedence_energy_v1', 'precedence_interval_energy_v2'):
        raise ValueError('certificate family')
    rows, upper, x = build_rows(raw, horizon, conditional,
                                interval_energy=family == 'precedence_interval_energy_v2')
    n, modes = raw["n"], raw["modes"]
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


def original_domains(raw):
    return [[m[0] for m in raw["modes"][j]] for j in range(1, raw["n"] + 1)]


def verify_tree(raw, horizon, witness, tree):
    check_witness(raw, witness, horizon)
    domains = original_domains(raw)
    counts = Counter()

    def visit(node, current):
        if set(node) == {"leaf_certificate"}:
            counts["leaves"] += 1
            return replay_certificate(raw, horizon, witness, node["leaf_certificate"], current)
        if set(node) != {"job_id", "mode_id", "included", "excluded"}:
            raise ValueError("tree node fields")
        j, mid = node["job_id"], node["mode_id"]
        if type(j) is not int or type(mid) is not int or not 1 <= j <= raw["n"]:
            raise ValueError("tree split index")
        if mid not in current[j - 1] or len(current[j - 1]) < 2:
            raise ValueError("tree split outside inherited domain")
        included = [list(d) for d in current]
        excluded = [list(d) for d in current]
        included[j - 1] = [mid]
        excluded[j - 1] = [m for m in excluded[j - 1] if m != mid]
        counts["splits"] += 1
        a = visit(node["included"], included)
        b = visit(node["excluded"], excluded)
        return min(a, b)

    lower = visit(tree["root"], domains)
    if tree.get("claimed_lb") != lower:
        raise ValueError("tree global claim mismatch")
    if lower > horizon:
        raise ValueError("covered tree exceeds feasible horizon")
    return {"integer_makespan_lb": lower, "leaves": counts["leaves"],
            "splits": counts["splits"],
            "input_sha256": hashlib.sha256(Path(raw["path"]).read_bytes()).hexdigest()}


def reject(fn):
    try:
        fn()
    except (AssertionError, KeyError, TypeError, ValueError):
        return True
    return False


def check_case(item):
    directory, source, live_row = item
    directory = Path(directory)
    claim = json.loads((directory / 'claim.json').read_text())
    name = claim['instance']
    raw = parse_mm(Path(source) / name)
    tree = json.loads((directory / 'tree.json').read_text())
    witness = json.loads((directory / 'witness.json').read_text())
    horizon = claim['scope']['H']
    got = verify_tree(raw, horizon, witness, tree)
    if got['integer_makespan_lb'] != claim['integer_lb']:
        raise ValueError(f'claim mismatch: {name}')
    if got['input_sha256'] != claim['scope']['input_sha256']:
        raise ValueError(f'source hash mismatch: {name}')
    if live_row['Ref1'] != name:
        raise ValueError(f'live name mismatch: {name}')
    live_lb, live_ub = int(live_row['LB value']), int(live_row['UB value'])
    lower, upper = max(live_lb, claim['live_LB']), min(live_ub, claim['live_UB'])
    lb = got['integer_makespan_lb']
    if not lower < lb <= upper:
        raise ValueError(f'fresh comparator gate failed: {name}: {lb} vs {lower}/{upper}')
    negative = {}
    bad = copy.deepcopy(tree)
    bad['claimed_lb'] += 1
    negative['wrong_global_bound'] = reject(lambda: verify_tree(raw, horizon, witness, bad))
    bad = copy.deepcopy(tree)
    leaf = bad['root']
    while 'leaf_certificate' not in leaf:
        leaf = leaf['included']
    leaf['leaf_certificate']['claimed_numerator'] += 1
    negative['corrupt_leaf_numerator'] = reject(lambda: verify_tree(raw, horizon, witness, bad))
    if got['splits']:
        bad = copy.deepcopy(tree)
        bad['root']['mode_id'] = -1
        negative['invalid_partition'] = reject(lambda: verify_tree(raw, horizon, witness, bad))
    bad_witness = copy.deepcopy(witness)
    bad_witness['mode_ids'][0] = 999999
    negative['invalid_witness'] = reject(lambda: verify_tree(raw, horizon, bad_witness, tree))
    if not all(negative.values()):
        raise AssertionError(f'negative control accepted: {name}: {negative}')
    return {'instance': name, 'lb': lb, 'previous_lb': claim['previous_certified_LB'],
            'live_lb': live_lb, 'live_ub': live_ub,
            'strongest_lb': lower, 'strongest_ub': upper,
            'delta_vs_previous': lb - claim['previous_certified_LB'],
            'delta': lb - lower, 'leaves': got['leaves'], 'splits': got['splits'],
            'source_sha256': got['input_sha256'], 'negative_controls': negative,
            'witness_horizon': horizon, 'matches_feasible_horizon': lb == horizon}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('result_dir', type=Path)
    ap.add_argument('--source-dir', type=Path, default=Path('data/mmlib/plus'))
    ap.add_argument('--workers', type=int, default=1)
    args = ap.parse_args()
    if args.workers < 1:
        ap.error('--workers must be positive')
    started = time.monotonic()
    data = urlopen(Request(URL, headers={'User-Agent': 'shutdown-schedule-repair/cold-tree'}), timeout=30).read()
    fetched_utc = datetime.now(timezone.utc).isoformat()
    digest = hashlib.sha256(data).hexdigest()
    (args.result_dir / 'MMplus_2.current.csv').write_bytes(data)
    lines = data.decode('latin1').lstrip('\ufeff').splitlines()
    start = next(i for i, line in enumerate(lines) if line.startswith('ID;'))
    live = {}
    for row in csv.DictReader(lines[start:], delimiter=';'):
        name = row.get('Ref1')
        if not name or not row.get('ID', '').isdigit():
            continue
        if name in live:
            raise ValueError(f'duplicate live filename: {name}')
        live[name] = row
    items = []
    for directory in sorted(args.result_dir.glob('Jall*')):
        if not (directory / 'claim.json').is_file():
            continue
        name = json.loads((directory / 'claim.json').read_text())['instance']
        items.append((str(directory), str(args.source_dir), live[name]))
    if not items:
        raise ValueError('no new candidate trees to verify')
    if args.workers == 1:
        rows = [check_case(item) for item in items]
    else:
        with ProcessPoolExecutor(max_workers=args.workers) as pool:
            rows = list(pool.map(check_case, items))
    negative = Counter(k for row in rows for k, passed in row['negative_controls'].items() if passed)
    result = {'live_url': URL, 'live_sha256': digest, 'live_fetched_utc': fetched_utc,
              'live_rows': len(live), 'trees': len(rows), 'cold_tree_replays': len(rows),
              'leaves': sum(row['leaves'] for row in rows),
              'splits': sum(row['splits'] for row in rows),
              'strict_live_rows': len(rows),
              'sum_delta_vs_fresh_live': sum(row['delta'] for row in rows),
              'extra_lb_units': sum(row['delta_vs_previous'] for row in rows),
              'negative_controls_rejected': dict(negative), 'rows': rows,
              'elapsed_seconds': time.monotonic() - started,
              'checker_origin': 'worker attempt-015 independent parser and integer replay; generic runner',
              'evidence_level': 'independently checked from original inputs; not submitted or accepted'}
    (args.result_dir / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'rows'}, indent=2))


if __name__ == '__main__':
    main()
