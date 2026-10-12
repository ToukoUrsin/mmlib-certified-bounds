"""Offline standard-library replay of the frozen combined MMLIB release."""
from __future__ import annotations

import argparse
import copy
import csv
import gzip
import hashlib
import json
import sys
import time
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path):
    data = path.read_bytes()
    if path.suffix == '.gz':
        data = gzip.decompress(data)
    return json.loads(data)


def check_case(item):
    packet, case = item
    packet = Path(packet)
    sys.path.insert(0, str(packet / 'checkers'))
    from verify_multimode_lp import verify as basic
    import verify_mmplus_cold_tree as ordinary
    import cg_replay
    import rounding_check
    import prefix_check
    import farkas_check

    path = packet / case['input']
    proof_path = packet / case['proof']
    if digest(path) != case['input_sha256'] or digest(proof_path) != case['proof_sha256']:
        raise ValueError('input/proof hash mismatch: ' + case['instance'])
    proof = load(proof_path)
    witness = case['witness']
    H = case['H']
    raw = ordinary.parse_mm(path)
    kind = case['proof_kind']

    def replay(p=proof, w=witness):
        if kind == 'certificate':
            return basic(path, H, w, p)['integer_makespan_lb']
        if kind == 'mode_tree':
            return ordinary.verify_tree(raw, H, w, p)['integer_makespan_lb']
        if kind == 'CG_tree':
            return cg_replay.verify(path, H, w, p)['integer_makespan_lb']
        if kind == 'rounding_tree':
            scope = {'H': H, 'witness': w, 'lb': case['claimed_LB']}
            return rounding_check.verify_tree(raw, scope, p)['lb']
        if kind == 'cumulative_prefix':
            return prefix_check.verify(proof_path.parent, path,
                                       certificate=p, horizon_witness=w)['proved_lb']
        if kind == 'time_indexed_farkas':
            return farkas_check.verify(path, p['h'], w, p, witness_H=H)['integer_makespan_lb']
        raise ValueError('unknown proof kind')

    bound = replay()
    if bound != case['claimed_LB'] or not case['strongest_LB'] < bound <= case['strongest_UB']:
        raise ValueError('bound/comparator mismatch')
    controls = []

    def reject(label, p=proof, w=witness):
        try:
            replay(p, w)
        except (ValueError, AssertionError, KeyError, TypeError):
            controls.append(label)
        else:
            raise AssertionError('negative accepted: ' + label)

    bad = copy.deepcopy(proof)
    if kind == 'certificate':
        bad['claimed_numerator'] += 1
    elif kind == 'cumulative_prefix':
        bad['proved_lb'] += 1
    elif kind == 'time_indexed_farkas':
        bad['certificate']['claimed_margin'] += 1
    else:
        bad['claimed_lb'] += 1
    reject('wrong_proof_claim', bad)
    badw = copy.deepcopy(witness)
    badw['mode_ids'][0] = 99999
    reject('invalid_original_mode', w=badw)
    if kind not in ('certificate', 'cumulative_prefix', 'time_indexed_farkas'):
        bad = copy.deepcopy(proof)
        node = bad['root']
        while 'included' in node:
            node = node['included']
        node['leaf_certificate']['claimed_numerator'] += 1
        reject('leaf_numerator', bad)
        if 'mode_id' in proof['root']:
            bad = copy.deepcopy(proof)
            bad['root']['mode_id'] = -1
            reject('invalid_partition', bad)
    if kind == 'CG_tree':
        bad = copy.deepcopy(proof)
        bad['CG_cuts'][0]['denominator'] = 0
        reject('invalid_CG_denominator', bad)
    if kind == 'rounding_tree':
        bad = copy.deepcopy(proof)
        node = bad['root']
        while 'included' in node:
            node = node['included']
        tr = node['leaf_certificate']['transforms'][0]
        tr['weights'][0] = tr['transformed_capacity'] + 1
        reject('invalid_resource_transform', bad)
    if kind == 'cumulative_prefix':
        bad = copy.deepcopy(proof)
        bad['survivors'].pop()
        reject('omitted_mode_branch', bad)
        bad = copy.deepcopy(proof)
        bad['shared_idle_budget'] -= 1
        reject('false_idle_budget', bad)
    return {'instance': case['instance'], 'set': case['set'], 'lb': bound,
            'delta': bound - case['strongest_LB'], 'proof_kind': kind,
            'original_optimality': bound == H, 'controls': controls}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--packet', type=Path, default=Path('.'))
    ap.add_argument('--workers', type=int, default=2)
    args = ap.parse_args()
    packet = args.packet.resolve()
    started = time.monotonic()
    manifest = load(packet / 'manifest.json')
    cases = load(packet / 'cases.json.gz')
    tables = {}
    for family, source in manifest['live_sources'].items():
        path = packet / source['file']
        if digest(path) != source['sha256']:
            raise ValueError('live snapshot hash mismatch')
        lines = path.read_text(encoding='latin1').splitlines()
        begin = next(i for i, line in enumerate(lines) if line.startswith('ID;'))
        rows = [r for r in csv.DictReader(lines[begin:], delimiter=';') if r.get('ID', '').isdigit()]
        if len({r['Ref1'] for r in rows}) != len(rows):
            raise ValueError('duplicate numeric live instance')
        tables[family] = {r['Ref1']: r for r in rows}
    if len({(c['set'], c['instance']) for c in cases}) != len(cases):
        raise ValueError('duplicate release row')
    for case in cases:
        row = tables[case['set']][case['instance']]
        rel = case['release_reference']
        if (case['strongest_LB'] != max(int(row['LB value']), rel['LB']) or
                case['strongest_UB'] != min(int(row['UB value']), rel['UB'])):
            raise ValueError('strongest comparator join mismatch')
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        checked = list(pool.map(check_case, [(str(packet), c) for c in cases]))
    counts = Counter(r['set'] for r in checked)
    deltas = Counter()
    for r in checked:
        deltas[r['set']] += r['delta']
    result = {'checked_rows': len(checked), 'families': dict(counts),
              'sum_LB_increase': sum(deltas.values()), 'family_LB_increase': dict(deltas),
              'proof_kinds': dict(Counter(r['proof_kind'] for r in checked)),
              'optimality_proofs': [r['instance'] for r in checked if r['original_optimality']],
              'negative_controls_rejected': sum(len(r['controls']) for r in checked),
              'seconds': time.monotonic() - started,
              'evidence_level': 'original-input exact offline replay; not submitted or accepted'}
    if counts != Counter(manifest['families']) or deltas != Counter(manifest['family_LB_increase']):
        raise ValueError('release aggregate mismatch')
    (packet / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2), flush=True)


if __name__ == '__main__':
    main()
