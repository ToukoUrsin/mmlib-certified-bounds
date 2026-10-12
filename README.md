# Certified lower bounds for MMLIB (multi-mode RCPSP)

1,423 MMLIB instances where we prove a makespan lower bound strictly above the best published one,
+9,977 units in total. Each bound comes with an exact proof and a Python checker (standard library only).

| Set | Improved rows | LB units gained |
|---|---:|---:|
| MMLIB+ (MMplus) | 1,382 | +9,903 |
| MMLIB100 | 33 | +65 |
| MMLIB50 | 8 | +9 |
| **Total** | **1,423** | **+9,977** |

- Comparator: the stronger of the live SolutionsUpdate lower bound
  ([MM50_4.csv](http://solutionsupdate.ugent.be/sites/default/files/datasets/MM50_4.csv),
  [MM100_4.csv](http://solutionsupdate.ugent.be/sites/default/files/datasets/MM100_4.csv),
  [MMplus_2.csv](http://solutionsupdate.ugent.be/sites/default/files/datasets/MMplus_2.csv))
  and the MMLIB v2.1 workbook lower bound. Every certified bound is at most the published upper bound.
  The three CSVs were re-fetched on 2026-10-12; their SHA-256 hashes match `release.json`, and all 1,423 rows
  are still strict improvements.
- No published upper bound is improved. 11 instances are closed (certified LB = published UB):
  J10011_4, J10012_2, J10012_3, J10046_2, J10046_5, Jall30_3, Jall30_5, Jall245_3, Jall353_2, Jall354_1, Jall434_2.
- Proof kinds: 1,013 LP/energy certificates, 403 mode-partition trees, 3 Chvatal-Gomory trees,
  2 rounding trees, 1 cumulative-prefix proof, 1 time-indexed Farkas certificate. Every proof works on the
  original `.mm` input: original modes, finish-start precedences, renewable capacities and nonrenewable budgets.

## Files

- `MMLIB-certified-LB.csv`: set, official ID, instance, strongest published LB, certified LB, published UB,
  witness makespan, closed flag, proof kind.
- `packet/`: original inputs, proofs, feasible witnesses, comparator snapshots, checkers (`packet/checkers/`)
  and `smoke.py`, which replays everything.
- Release asset `verification-packet.tar.gz`: the same packet as one archive (SHA-256 in `archive.json`).

## Verify

```bash
cd packet
python3 -S smoke.py --workers 4
```

Python 3 standard library only, offline, no optimizer. A cold replay on 4 vCPUs took 61 s:
1,423/1,423 proofs accepted and 3,663/3,663 deliberately corrupted controls rejected
(wrong bound, altered certificate, invalid witness, shifted source). The result is in `packet/verification.json`.

The original instances come from the MMLIB library (Van Peteghem and Vanhoucke 2014,
https://www.projectmanagement.ugent.be/research/data). They are included only so the proofs can be checked.

Contact: Touko Ursin, touko.ursin@gmail.com
