Run `python3 -S smoke.py --workers 2` from this folder. Python standard library only, offline, no optimizer.

This packet contains 1,423 original MMLIB inputs, exact proofs, feasible witnesses, comparator snapshots and independent checkers. The score is the certified integer lower bound minus the stronger of the live and public v2.1 lower bounds, with the tighter published upper bound as a feasibility gate. Release 041 totals +9,977 units: MMplus 1,382 rows/+9,903, MM100 33/+65 and MM50 8/+9.

The new `time_indexed_farkas` case is Jall245_3.mm: an exact original-mode time-indexed LP dual ray excludes horizon 64, while its independently checked original witness completes at 65. This raises the release bound from 64 to 65, matching the public UB and proving that original makespan locally. Its checker reconstructs every legal activity/mode/start column, finish-start CDF rows, half-open renewable rows and nonrenewable budgets with integer arithmetic.

The other proof families retain original modes, finish-start precedences, renewable capacities and nonrenewable budgets. The replay checks comparator joins, proof hashes, witnesses and deliberately corrupted controls. Official SolutionsUpdate validator binaries have not been run on Linux.

`verification.json` records the complete replay result. `archive.json` records the part hashes and concatenated archive hash. No submission or acceptance has occurred.
