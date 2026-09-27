# Fresh Lean acceptance — 9 September 2026

Isolated workflow run [34373066035](https://github.com/dicipler-pixel/operator-first/actions/runs/34373066035) completed successfully at source commit `7419083917f4c08df70a0381bfee0693f3b504fb`. Its artifact was downloaded and inspected.

All 21 named declarations in `lean/GaugeCertificates.lean` compile under Lean 4.33.0 (compiler commit `d8b18978322de05a8f3dba51ef03cf5461676c17`) and mathlib commit `db584cd6d46c92f209a44c0f1c829460d327499d`. Each explicit axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`. No admitted/custom axiom or native-decision axiom occurs. The deliberately false arithmetic statement fails with `unsolved goals` and goal `False` after valid imports.

The compiled source SHA-256 is `6e24b7257c575e36017d9cfacfd60696473413e2f1b60a3a5b2ea14ca221402d`, exactly matching the local delivered source. Lean-toolchain SHA-256: `302cd63c54178885b89e669f33b38f12f4dd7ae7e5cac537b3203e3768d8fb2b`. Lakefile SHA-256: `c4dc6a633174d88933f545b0e8ca2884b315e83a3a9849a4f375eddf30708a14`.

## Actual formal scope

The two matrix identities are complete exact rational LDL factorizations of the displayed 10x10 inner and 7x7 outer matrices. Triangularity, unit diagonal, pivot signs, and the allocation/test-energy arithmetic are also accepted. Together with the separately written analytic arguments they support the simple full-tail gap certificate >=4 for the shared-link two-plaquette model at alpha=lambda=1.

The module does **not** formalize Haar integration, the completeness of the physical gauge basis, positivity improvement, infinite-dimensional Schur inertia, the local-window/gap-transfer theorem, the volume-uniform stability theorem, or the continuum Yang–Mills construction. A separate Leanchecker replay was not performed.

## Failed attempts retained

Run 34368109558: direct `decide` was unsuitable for the dependent finite matrix and rational reductions. Run 34370073443: explicit index cases left vector-times-diagonal expressions and one third-entry evaluation unreduced. The final repair supplied the specific matrix simplification lemmas; no mathematical statement was weakened. Failure and success logs are preserved in the local evidence package. Root repository CI is not substituted for this isolated verification.
