"""Dependency-free checker for a time-indexed original-mode Farkas ray."""
import hashlib
from pathlib import Path


def _reconstruct(raw, H):
    n, ms, succ = raw["n"], raw["modes"], raw["succ"]
    nr, nn, caps = raw["nr"], raw["nn"], raw["caps"]
    pred = {j: [] for j in ms}
    for j, ss in succ.items():
        for s in ss:
            if not j < s <= n: raise ValueError("non-topological source")
            pred[s].append(j)
    minimum = {j: min(m[1] for m in row) for j, row in ms.items()}
    early = {}; tail = {}
    for j in range(1, n + 1): early[j] = max([early[a] + minimum[a] for a in pred[j]] + [0])
    for j in reversed(range(1, n + 1)): tail[j] = max([tail[a] + minimum[a] for a in succ[j]] + [0])
    columns = []; jc = {j: [] for j in ms}
    for j in range(1, n + 1):
        for k, (_, d, qs) in enumerate(ms[j]):
            for t in range(early[j], H - tail[j] - d + 1):
                if j == 1 and t != 0: continue
                jc[j].append(len(columns)); columns.append((j, k, t))
        if not jc[j]: raise ValueError("empty column domain")
    def rows():
        links = list(dict.fromkeys([(j, s) for j in range(1, n + 1) for s in succ[j]] + [(j, n) for j in range(1, n)]))
        for j, s in links:
            for tick in range(H):
                before = [i for i in jc[j] if columns[i][2] + ms[j][columns[i][1]][1] <= tick]
                after = [i for i in jc[s] if columns[i][2] <= tick]
                if not after or len(before) == len(jc[j]): continue
                yield [(i, -1) for i in before] + [(i, 1) for i in after], 0
        for r in range(nr):
            for tick in range(H):
                yield ([(i, ms[j][k][2][r]) for i, (j, k, t) in enumerate(columns)
                        if t <= tick < t + ms[j][k][1] and ms[j][k][2][r]], caps[r])
        for r in range(nn):
            yield ([(i, ms[j][k][2][nr + r]) for i, (j, k, t) in enumerate(columns)
                    if ms[j][k][2][nr + r]], caps[nr + r])
    return columns, jc, rows


def _witness(raw, witness, H):
    starts, mids = witness["starts"], witness["mode_ids"]
    if len(starts) != raw["n"] or len(mids) != raw["n"]: raise ValueError("witness shape")
    selected = []
    for j, mid in enumerate(mids, 1):
        found = {m[0]: m for m in raw["modes"][j]}
        if mid not in found: raise ValueError("invalid witness mode")
        selected.append(found[mid])
    ends = [s + m[1] for s, m in zip(starts, selected)]
    if starts[0] != 0 or starts[-1] != max(ends) or starts[-1] != H: raise ValueError("witness horizon")
    for j, ss in raw["succ"].items():
        if any(ends[j - 1] > starts[s - 1] for s in ss): raise ValueError("witness precedence")
    for r in range(raw["nn"]):
        if sum(m[2][raw["nr"] + r] for m in selected) > raw["caps"][raw["nr"] + r]: raise ValueError("witness budget")
    for t in range(H):
        for r in range(raw["nr"]):
            if sum(m[2][r] for s, e, m in zip(starts, ends, selected) if s <= t < e) > raw["caps"][r]: raise ValueError("witness renewable")


def verify(path, H, witness, record, witness_H=None):
    from farkas_raw_parse import parse_mm
    raw = parse_mm(path); _witness(raw, witness, H if witness_H is None else witness_H)
    if hashlib.sha256(Path(path).read_bytes()).hexdigest() != record.get("source_sha256"): raise ValueError("source hash")
    c = record.get("certificate", {})
    if c.get("row_family") != "time_indexed_farkas_v1" or c.get("h") != H or c.get("energy") or c.get("expected"): raise ValueError("certificate family")
    D, ys, zs = c.get("denominator"), c.get("inequality_dual_integers"), c.get("equality_dual_integers")
    if type(D) is not int or D <= 0 or len(zs) != raw["n"] or any(type(z) is not int for z in zs) or any(type(y) is not int or y > 0 for y in ys): raise ValueError("dual dimensions/sign")
    cols, jc, rows = _reconstruct(raw, H); residual = [0] * len(cols); beta = sum(zs); count = 0
    for entries, b in rows():
        if count >= len(ys): raise ValueError("missing rows")
        y = ys[count]; count += 1; beta += b * y
        for i, a in entries: residual[i] -= a * y
    if count != len(ys): raise ValueError("extra rows")
    for j in range(1, raw["n"] + 1):
        for i in jc[j]: residual[i] -= zs[j - 1]
    correction = sum(min(0, x) for x in residual); margin = beta + correction
    if (margin != c.get("claimed_margin") or beta != c.get("beta") or correction != c.get("box_correction") or margin <= 0): raise ValueError("dual identity")
    return {"integer_makespan_lb": H + 1, "columns": len(cols), "inequality_rows": count, "margin": margin}
