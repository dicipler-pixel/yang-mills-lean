# Formal scope — compiled successfully

All 21 named declarations compile in isolated GitHub Actions run [34373066035](https://github.com/dicipler-pixel/operator-first/actions/runs/34373066035), source commit `7419083917f4c08df70a0381bfee0693f3b504fb`, Lean/mathlib 4.33.0. Every axiom audit contains only propext, Classical.choice, and Quot.sound. FalseControl.lean is rejected on a mathematical goal. See `../reports/03_lean_acceptance.md` for hashes and failed-attempt history.

The declarations check closed rational arithmetic for a nested certificate of gap at least 4 in the two-plaquette SU(3) model at alpha=lambda=1. The inner 10-by-10 matrix certifies a proposed single-plaquette ground lower bound 21/10 when kappa=21/40; the outer 7-by-7 matrix uses s=17/20, d=182/15, r=6, z=10.

Successful compilation checks the displayed matrix factorizations, unit triangularity, pivot signs, and normalization arithmetic. Haar integration, completeness of the gauge subspace, the analytic infinite-tail bound, and Schur inertia are written proofs outside this module. Do not describe this as a formal quantum Yang–Mills or continuum proof.
