"""Cold, standard-library-only replay of the pass-002 MMLIB+ trees.

The tree checker parses each original ``.mm`` file, reconstructs the
precedence/energy inequalities, and recomputes every saved rational dual with
integer arithmetic.  It also checks the supplied feasible horizon witness,
the exact source-mode partition at every split, a fresh public live-table
join, and deliberately corrupted controls.  No repository checker or solver
is imported.
"""
from __future__ import annotations

import copy
import csv
import hashlib
import json
import re
import time
from collections import Counter, defaultdict
from pathlib import Path
from urllib.request import Request, urlopen


ROOT = Path.cwd().resolve()
HERE = Path(__file__).resolve().parent
SOURCE = ROOT / "data" / "mmlib" / "plus"
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


def fetch_live():
    data = urlopen(Request(URL, headers={"User-Agent": "shutdown-schedule-worker/015"}), timeout=30).read()
    digest = hashlib.sha256(data).hexdigest()
    (HERE / "MMplus_2.current.csv").write_bytes(data)
    lines = data.decode("latin1").lstrip("\ufeff").splitlines()
    start = next(i for i, line in enumerate(lines) if line.startswith("ID;"))
    rows = {r["Ref1"]: r for r in csv.DictReader(lines[start:], delimiter=";") if r.get("Ref1")}
    return digest, rows


def main():
    started = time.monotonic()
    live_digest, live = fetch_live()
    out = []
    negative = Counter()
    errors = []
    dirs = sorted(p for p in HERE.glob("Jall*") if (p / "claim.json").exists())
    for directory in dirs:
        claim = json.loads((directory / "claim.json").read_text())
        name = claim["instance"]
        path = SOURCE / name
        raw = parse_mm(path)
        tree = json.loads((directory / "tree.json").read_text())
        witness = json.loads((directory / "witness.json").read_text())
        got = verify_tree(raw, int(claim["scope"]["H"]), witness, tree)
        if got["integer_makespan_lb"] != claim["integer_lb"]:
            raise ValueError(f"claim mismatch {name}")
        if got["input_sha256"] != claim["scope"]["input_sha256"]:
            raise ValueError(f"source hash mismatch {name}")
        row = live.get(name)
        if row is None:
            raise ValueError(f"missing live row {name}")
        live_lb, live_ub = int(row["LB value"]), int(row["UB value"])
        lb = got["integer_makespan_lb"]
        if not (lb > live_lb and lb <= live_ub):
            raise ValueError(f"fresh live gate failed {name}: {lb} vs {live_lb}/{live_ub}")

        bad = copy.deepcopy(tree)
        bad["claimed_lb"] += 1
        if not reject(lambda: verify_tree(raw, int(claim["scope"]["H"]), witness, bad)):
            raise AssertionError(f"wrong global bound accepted: {name}")
        negative["wrong_global_bound"] += 1

        bad = copy.deepcopy(tree)
        leaf = bad["root"]
        while "leaf_certificate" not in leaf:
            leaf = leaf["included"]
        leaf["leaf_certificate"]["claimed_numerator"] += 1
        if not reject(lambda: verify_tree(raw, int(claim["scope"]["H"]), witness, bad)):
            raise AssertionError(f"corrupt leaf accepted: {name}")
        negative["corrupt_leaf_numerator"] += 1

        if got["splits"]:
            bad = copy.deepcopy(tree)
            bad["root"]["mode_id"] = -1
            if not reject(lambda: verify_tree(raw, int(claim["scope"]["H"]), witness, bad)):
                raise AssertionError(f"invalid partition accepted: {name}")
            negative["invalid_partition"] += 1

        badw = copy.deepcopy(witness)
        badw["mode_ids"][0] = 999999
        if not reject(lambda: verify_tree(raw, int(claim["scope"]["H"]), badw, tree)):
            raise AssertionError(f"invalid witness accepted: {name}")
        negative["invalid_witness"] += 1
        out.append({"instance": name, "lb": lb, "live_lb": live_lb,
                    "live_ub": live_ub, "delta": lb - live_lb,
                    "leaves": got["leaves"], "splits": got["splits"],
                    "source_sha256": got["input_sha256"]})

    summary = {"live_url": URL, "live_sha256": live_digest,
               "trees": len(out), "cold_tree_replays": len(out),
               "leaves": sum(r["leaves"] for r in out),
               "splits": sum(r["splits"] for r in out),
               "strict_live_rows": sum(r["lb"] > r["live_lb"] for r in out),
               "sum_delta_vs_fresh_live": sum(r["delta"] for r in out),
               "negative_controls_rejected": dict(negative),
               "rows": out, "elapsed_seconds": time.monotonic() - started,
               "evidence_level": "independently checked cold replay; not submitted or accepted"}
    (HERE / "verification.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
