# Certified Ky Fan chord gap bounds: one plaquette (λ = 8) and the two-square cell (Green, 2026-11-11)

Jeromie Beasley research programme. Credit: Green.
GitHub [dicipler-pixel](https://github.com/dicipler-pixel) · X [@d1c1pler](https://x.com/d1c1pler) ·
YouTube [@AtlasMemoriae](https://www.youtube.com/@AtlasMemoriae) · site
[atlas-memoriae.dicipler.workers.dev](https://atlas-memoriae.dicipler.workers.dev) ·
ORCID [0009-0006-4645-5643](https://orcid.org/0009-0006-4645-5643)

## Setup
- Source question: the open-questions ledger v2, votkp-lean commit 9a67163,
  [research/2026-11-11/open_questions/](https://github.com/dicipler-pixel/votkp-lean/tree/9a671632931985dba11a05df239e2541e1105d03/research/2026-11-11/open_questions).
  Item 3 there (`open_tests_05.py`, test T2) is the float Ky Fan chord this folder certifies. No ledger code is needed:
  the scripts here rebuild the same Hamiltonians and only quote the ledger's numbers for comparison.
- Imports are repo-relative: `common_plaq.py` and `common_theta.py` put `../../yang_mills_2026_09_09/scripts` and
  `../../yang_mills_2026_09_09/cross_theorem/scripts`, taken relative to this folder, on `sys.path`. They use
  `su3_character_certificate.interval_inertia`, `two_plaquette_19` and `two_plaquette_certificate.exact_inertia`
  unchanged. The method is the same as `research/2026-11-10/window_wall_endpoints/certify_slopes.py`: exact
  outward-interval or rational LDL inertia with a Schur tail.
- Run from anywhere with `OMP_NUM_THREADS=1 python3 research/2026-11-11/kyfan_chord/<script>.py`. Outputs are written
  next to the scripts. Run order: `kyfan_plaquette.py`; `theta_reference.py` (about 15 min, K = 4), then `kyfan_theta.py`
  (it reads `theta_reference.json`); `check_19.py`. Needs Python 3, NumPy and SciPy.
- Rerun check from this folder (run from `/tmp`, so the cwd is unrelated): `kyfan_plaquette.out` and its JSON came out
  identical, apart from the elapsed time. `check_19.out` came out identical. The two-square node certificates at λ = 1 and
  λ = 4 reproduced the exact rationals stored in `kyfan_theta.json`.

## Definitions found (ledger normalisation)
One plaquette: `H(κ, λ) = κ C2 + λ(3 − Re χ_(1,0))` on class functions of the plaquette holonomy, orthonormal character
basis (p,q): diag κ c(p,q) + 3λ, six neighbours −λ/2. λ = 8 fixed, **chord in κ**, ledger chord κ ∈ [1/2, 2] evaluated
at κ = 0.75…1.75. `E_i(κ,8) = κ e_i(8/κ)` with e_i the levels of `C2 + μ(3 − Re χ)` (repo κ = 1 form).
Two-square cell: two squares sharing one link (theta graph, arms 1,3,3), `H(λ) = E_el + λ(6 − Re TrU − Re TrV)`, α = 1
(repo 19-state cell, ledger item 1, λ = 0.1…4). **Chord in λ.**
In both cases H is affine in the chord variable, so S = E0 + E1 is concave and
`gap(x) ≥ chord_lo(x) − 2·E0_up(x)` for x in [a,b].

**Sector.** Both are the whole gauge-invariant (physical) space: all class functions for one plaquette, all
vertex-gauge-invariant spin networks for the theta graph. No charge-conjugation split. E0 and E1 are the lowest two levels
of that whole space, the same sector the ledger's gap and the 19-state certificate use. Float check on one plaquette at
κ = 1, λ = 8: E0 and E1 are C-even, E2 is C-odd.

## What is certified (exact) and how
- **E0 ≥ z0, E1 ≥ z1 at chord ends (multiplicity counted).** One plaquette: repo `interval_inertia(N=40, μ, z, schur=True)`
  gives 0 or ≤ 1 negative pivots. By Haynsworth plus tail ≥ d, H − z has at most that many eigenvalues below z.
  Two squares: the exact 19×19 form `K(z) = A − zG − λ²M/(d−z)` (repo `exact_inertia`) gives 0 or ≤ 1 negative pivots,
  with d = s·43/3 + 2e. The inner floor e is certified by the repo `interval_inertia`, exactly as in `certify_row`, and s is
  picked from a grid. At λ = 0 the electric spectrum is exact: S(0) = 0 + 16/3.
- **E0 ≤ E0_up at every interior point.** These are exact rational Rayleigh quotients of fixed finite-support trial vectors
  (rationalised float eigenvectors) in the full space, not truncated eigenvalues. One plaquette: character basis, exact
  ⟨C2⟩ and ⟨3 − Re χ⟩. Two squares: the 19 exact Haar functions with exact G, S. Each quotient is affine in the chord
  variable, so one vector bounds E0 at *every* point. I use the minimum over several tangent vectors. That is why each chord
  piece also gets a bound valid for **all** x in [a,b]: the bound is convex piecewise linear, so its exact minimum is at a
  vertex, and I evaluate every candidate vertex.
- **Controls.** Shifts 1/1000 (plaquette) or 1/100 (theta) above a certified lower bound are rejected, because the negative
  pivot count goes up. Every Rayleigh quotient sits above its certified E0 lower bound.
- **Float only:** the "exact" gaps, the ledger-style float chords, and the worst-ratio scans.
  One plaquette: dense, N = 64. Two squares: `sn_theta.py`, an independent spin-network Galerkin solver.
  Restricted to electric ≤ 40/3 it reproduces the repo's 19-state pencil to 4e-14 at λ = 0, 0.1, 1, 4 (`check_19.py`).
  K=3→4 gap change is 7e-3 at λ = 4 and 1e-4 at λ = 2; successive-change ratio ≈0.04, so K=4 is good to ≈3e-4.

## One plaquette, λ = 8 (`kyfan_plaquette.py` → `.out`, `.json`)
A. Ledger chord [1/2, 2]:

| κ | exact gap | ledger float chord | **certified** | cert / float chord | loss vs exact |
|---|---|---|---|---|---|
| 0.75 | 4.39318 | 3.21581 | 3.21581155 | 1.0000000 | 26.8% |
| 1.00 | 4.97290 | 3.33038 | 3.33037527 | 1.0000000 | 33.0% |
| 1.25 | 5.45834 | 3.80781 | 3.80781366 | 1.0000000 | 30.2% |
| 1.50 | 5.87568 | 4.54351 | 4.54350591 | 1.0000000 | 22.7% |
| 1.75 | 6.24043 | 5.47529 | 5.47529052 | 1.0000000 | 12.3% |

Certification keeps essentially all of the exact chord. The cost is about 1e-8, since S_lo(1/2) and S_lo(2) are within 1e-10
of exact. All of the loss belongs to the chord itself. Note: the ledger says "15 to 33%", but its own numbers give 12.3–33.0%.

B. Single chords, certified for every κ in [a,b]:

| [a,b] | certified min gap on [a,b] | worst cert/exact (float scan) |
|---|---|---|
| [0.5,2] | 3.1698 | 0.667 |
| [0.75,1.75] | 4.3393 | 0.870 |
| [0.5,1.25] | 3.6129 | 0.854 |
| [1.25,2] | 5.4583 | 0.958 |
| [0.5,1] | 3.6637 | 0.916 |
| [1,1.5] | 4.9729 | 0.970 |
| [1.5,2] | 5.8757 | 0.984 |
| [0.25,4] | −0.880 | useless |

The best single chord through the ledger's five points is [0.75, 1.75], which keeps ≥ 87% of the gap everywhere on it.
Shorter chords are always better, so the useful object is a cover.

C. Covering [1/2, 2] with K equal chords (exact min gap on [1/2,2] is 3.66807, at κ = 1/2):
K = 1: 3.1140 (worst kept 65%) · K = 2: 3.5619 (85%) · K = 3: 3.6595 (91%) · K = 6: 3.66807 (97%) · K = 12: 3.66807 (99.1%).
With 6 or more pieces, the certified bound for all κ in [1/2, 2] equals the true minimum gap to 1e-6.

## Two-square cell, λ ∈ [0, 4] (`kyfan_theta.py` → `.out`, `.json`; reference `theta_reference.py` → `.out`, `.json`)
Best cover tried, nodes every 1/4 (pointwise values; exact gap from K = 4):

| λ | certified chord gap ≥ | exact gap | loss | ledger direct 19-state cert |
|---|---|---|---|---|
| 0.10 | 5.2794 | 5.2841 | 0.1% | 5.284 |
| 0.25 | 5.2131 | 5.2131 | 0.0% | |
| 0.50 | 5.1028 | 5.1032 | 0.0% | 5.103 |
| 0.75 | 5.0024 | 5.0051 | 0.1% | |
| 1.00 | 4.9088 | 4.9200 | 0.2% | 4.909 |
| 1.50 | 4.6981 | 4.7943 | 2.0% | |
| 2.00 | 4.2598 | 4.7351 | 10.0% | 4.274 |
| 2.50 | 3.3687 | 4.7480 | 29.0% | |
| 3.00 | 2.2195 | 4.8343 | 54.1% | 2.467 |
| 3.50 | 1.0294 | 4.9897 | 79.4% | |
| 4.00 | −0.6128 | 5.2055 | fails | 0.991 |

Uniform certified bounds, valid for every λ in the piece: [0,1/4] ≥ 5.2131, [1/4,1/2] ≥ 5.1028, [1/2,3/4] ≥ 5.0024,
[3/4,1] ≥ 4.9088, [1,1.25] ≥ 4.8136, [1.25,1.5] ≥ 4.6981, [1.5,1.75] ≥ 4.5283, [1.75,2] ≥ 4.2598,
[2,2.25] ≥ 3.8667, [2.25,2.5] ≥ 3.3687, [2.5,2.75] ≥ 2.8082, [2.75,3] ≥ 2.2195, [3,3.25] ≥ 1.6232,
[3.25,3.5] ≥ 1.0294, [3.5,3.75] ≥ 0.4424, [3.75,4] fails. **So the gap is certified ≥ 4.2598 for every λ in [0, 2],
and > 0 for every λ in [0, 3.75].** The ledger's direct certificates cover only six isolated points.
The other designs are in the `.out` file: a single chord [0,4] is positive only up to λ ≈ 2.4, and ledger-node chords
{0,0.1,0.5,1,2,3,4} lose 7% at 1.5, 34% at 2.5 and 85% at 3.5.

**Where the loss comes from (two squares).** It does not come from the chord: the float chord with exact endpoints and
exact E0 stays within 2% of the gap on the 1/4 cover. It comes from the certified node bounds. The 19-state Schur lower
bounds fall away from the true levels once λ ≳ 1.5 (E1 − z1 = 0.46 at λ = 2, 2.3 at 3, 3.95 at 4; E0 − z0 = 1.34 at 4),
because the hidden floor d (18.9 to 23.5) gets close. The 19-state Rayleigh–Ritz E0_up adds 0.26 of excess at λ = 4.
At a node the chord gives z0 + z1 − 2r = (z1 − r) − (r − z0), so it is always below the ledger's direct z1 − r. The chord
pays off between nodes, not at them.

## Why λ = 4 fails, and what would move it
The failure at λ = 4, and the large losses from λ ≈ 2.5 up, come from the 19-state Schur node floors: the certified
E0 and E1 lower bounds at the chord ends. They do not come from the chord or the trial vectors. This is the same blocker
as the ledger's "not testable tonight" entry for the large-λ SU(3) two-square gap: it needs an SU(3) recoupling (6j) or
Gelfand–Tsetlin build, because the exact Haar machinery stops at degree 6. A bigger exact basis would raise the hidden
floor d and tighten both the node lower bounds and the E0 Rayleigh–Ritz upper bound. It would therefore move this
chord certificate and the ledger's direct 19-state certificate together. `sn_theta.py` is a float version of such a
spin-network build; making it exact (rational CG/6j data) is the natural next step.

## Caveats
- Exact Python arithmetic, not Lean. Nothing here is a Lean theorem, and no Lean file is changed.
- The two-square certificates rely on `research/yang_mills_2026_09_09/proofs/TWO_PLAQUETTES.md` (completeness of the
  19-state electric cutoff), on the hidden-floor allocation d = s·43/3 + 2e, and on the repo's exact Haar code.
- The trial vectors and test shifts are chosen from float computations. Only the exact inertia counts and the exact
  Rayleigh quotients carry the proof.
- The "exact gap" columns are float references (dense N = 64 for one plaquette, `sn_theta.py` K = 4 for the two-square
  cell, with values between table points from K = 3, which agrees with K = 4 to within 1e-3).
- Finite graphs only. There is no continuum claim and no volume-uniform claim, and no continuum mass gap is claimed.
