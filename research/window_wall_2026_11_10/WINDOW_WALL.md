# The window wall for the C<=8 complete-tail certificate

Jeromie Beasley research programme — 10 November 2026. Written derivation plus exact checks.
Not a Lean theorem. It excludes; it does not prove a gap and does not locate the real edge.

## Statement

On a finite graph with faces p, allocation coefficients c_p (sum over the face's links of
1/(faces on that link)), and one-plaquette ground energy g(kappa) of
kappa*C2 + lambda*(3 - Re chi):

    d - r <= W(s) = s*(28/3) - sum_p [ g(c_p) - g((1-s)*c_p) ],   0 < s <= 1.

W(0) = 0 and W is concave, so if

    sum_p c_p * g'_right(c_p) >= 28/3

then W(s) <= 0 for every s and no certificate r < z < d of this class exists.

## Derivation

1. LOCAL_ENERGY_FLOORS.md (2): d = s*(28/3) + sum_p e_p, and each certified local floor
   obeys e_p <= g((1-s)*c_p).
2. The same allocation with all electric weight given to the faces (s = 0) gives
   H >= sum_p g(c_p), so r >= E0 >= sum_p g(c_p).
3. Subtract.
4. kappa*C2 + lambda*(3 - Re chi) is linear in kappa, so g is a minimum of straight lines
   and is concave. g((1-s)*c_p) is concave in s; hence W is concave.
5. The slope of W at s = 0 uses the left derivative of g at c_p, which for a concave
   function is at least the right derivative. So W'(0) <= 28/3 - sum_p c_p g'_right(c_p).
6. Forward secant: g'_right(c) >= (g_low(c+h) - g_up(c))/h for certified endpoints.

Derivative-free form (the version formalized in yang-mills-lean PR #5, `WindowWallFinite.lean`):
with L_p = (g_low(c_p+h_p) - g_up(c_p))/h_p, concavity gives g(c_p) - g((1-s)c_p) >= s*c_p*L_p,
so W(s) <= s*(28/3 - sum_p c_p L_p) for every s in (0, 1]. No derivatives or level-crossing
care are needed.

Inputs and limits. 28/3 is the repo's tail floor on the total Casimir C = sum_e C_e over
gauge-invariant states (`spatial_gauge.py`, `tail=F(28,3)`, `cutoff=F(8)`); it is not C2(4,0)
(C2(3,1) = 25/3 lies between 8 and 28/3). Step 2 is LOCAL_ENERGY_FLOORS.md (1) at beta = 0, with
s = 0 as its limiting case. Everything is at alpha = 1 and for the even allocation
a_pe = (1-s)/r_e only.

## Certified result (window_wall_certified_02.py; integer intervals on the 2^-192 grid, N = 30, h = 1/1000)

g_low: the one-loop complete-tail Schur matrix has no negative pivot (the test already used
for local floors). g_up: the finite retained matrix has a negative pivot (Rayleigh–Ritz).

| Graph | Faces | Excluded for lambda/alpha at and above (tested 1,2,3,4,5,6,8,10) |
|---|---:|---:|
| Two squares | 2 | 8 |
| Three-square strip | 3 | 5 (margin -0.124) |
| Three-face corner | 3 | 5 (margin -0.420) |
| Cube | 6 | 3 |
| Two adjacent cubes | 11 | 2 |

Control: none of the 58 stored accepted targets lies in an excluded cell, and all 58 obey
d - r <= W(s) (window_wall_01.py, float check, smallest slack 0.000276).

## Why "at and above" holds between and beyond the tested couplings

Write g(kappa, lambda) = kappa*e(lambda/kappa) with e(t) = g(1, t), which is concave in t
(a minimum of straight lines). Then dg/dlambda (kappa, lambda) = e'(lambda/kappa). Raising kappa
lowers lambda/kappa, and e' is non-increasing, so dg/dlambda is non-decreasing in kappa
(using one-sided derivatives where needed). Hence g(c+h, lambda) - g(c, lambda) is
non-decreasing in lambda. The true forward secants therefore only grow with lambda, while c_p and
28/3 do not depend on lambda, so a certified exclusion at a tested lambda/alpha excludes every
larger coupling for the same graph and allocation class.

## Exact check of the 58 stored windows (certify_58_windows.py)

Using certified lower endpoints for g((1-s)c_p) and upper endpoints for g(c_p) gives a rational
lower bound W_low(s) <= W(s), compared directly with the stored rational d - r. All 58 obey
d - r <= W_low(s) <= W(s); the smallest certified slack
is 275749/10^9 (two squares, lambda/alpha = 1/10, s = 1). Green's certify_58_windows.py (this folder,
output in certify_58_windows_N20.out) reproduces it with 0 violations and smallest slack
0.000275882; the small difference from 0.000275749 is from looser endpoints. The float check in window_wall_01.py
agrees (smallest slack 0.000276).

## What it does not say

Two cubes at lambda/alpha = 1 is not excluded here, and the stored search there was
inconclusive. That case is still open: the bound is an outer bound only, and it does not say
whether a certificate exists there. The bound applies to
the total-electric cutoff C <= 8 with floor 28/3 only. It is the finite-graph form of the
fixed-total-cutoff obstruction in SCALING_AND_OBSTRUCTIONS.md.

## 2026-11-10 late results

These were checked after the sections above were written. Where they conflict with
"What it does not say", this section is the newer status.

- **Uneven splits.** Splits that differ across faces but keep a common retained electric
  fraction s on every link cannot reopen any of the five cells. Proof: g is concave and
  nondecreasing, so by Jensen the equal face coefficient c = E/P is optimal. Certified
  lower bounds on the exclusion margin delta (GPT's values):

  | cell | lambda | c | delta (GPT, certified) | Grey rerun, h = c/1000 |
  |---|---|---|---|---|
  | two squares | 8 | 7/2 | >= 1.452038 | 1.4482 |
  | strip | 5 | 10/3 | >= 0.138547 | 0.1343 |
  | corner | 5 | 3 | >= 0.421398 | 0.4175 |
  | cube | 3 | 2 | >= 2.031478 | 2.0278 |
  | two cubes | 2 | 20/11 | >= 2.601404 | 2.5971 |

- **Any alpha.** The results hold for every alpha > 0 at the same ratio mu = lambda/alpha.
- **Double cube.** For the repo's C <= 8 certificate, the double cube is excluded for all
  lambda/alpha >= 0.9867 (GPT/Astra: 95 x 95 retained matrix, integer-interval check).
  The certificate is accepted at lambda/alpha = 0.5. The exact edge between 0.5 and 0.9867
  is open.
- **Graph step.** On all five graphs, every leaf-free support with at most 6 links is a
  single 4-cycle or 6-cycle. Counts (4-cycles / 6-cycles): two squares 2/1, strip 3/2,
  corner 3/4, cube 6/16, two cubes 11/36. Independent counts by GPT and Green; Lean kernel
  proof (`SmallSupportsAreCycles`, no symmetry shortcut) in PR #11.
- **Still open:** the SU(3) gauge support rule (no dangling link; conjugate irreps at
  two-valent vertices), link-dependent s, the exact double-cube edge, and the 40/3 and
  43/3 floors in Lean.
