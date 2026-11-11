# Spectrum dictionary and SU(3) theta enumeration (2026-11-10)

Research notes only. Nothing here is a Lean file, and the lakefile, config and gate are untouched.

- `dictionary.md`: the team's running dictionary for the Yang–Mills window-wall plan. It separates standard physical quantities from our own constructions, and records each night's results, corrections and frozen-statement edits.
- `theta.py`: an exact enumeration of SU(3) labellings on the theta graph with arms of 1, 3 and 3 links. It uses Gelfand–Tsetlin weights and Racah–Speiser tensor products, and self-tests 3⊗3, 3⊗3̄ and 8⊗8. It covers every irrep with p+q ≤ 6, which is complete below level 17.
- `theta.out`: the output, with 34 admissible rows and levels 16/3, 8, 28/3, 11, 34/3, 12, 40/3, 43/3, 46/3, 49/3 and 17. `ThetaFloor.lean` (Lean Green) proves the same list.

Rerun it with `python3 theta.py > theta.out`.

Jeromie N. Beasley: GitHub [dicipler-pixel](https://github.com/dicipler-pixel), X [@d1c1pler](https://x.com/d1c1pler), YouTube [@AtlasMemoriae](https://www.youtube.com/@AtlasMemoriae), [Atlas Memoriae](https://atlas-memoriae.dicipler.workers.dev), ORCID https://orcid.org/0009-0006-4645-5643
