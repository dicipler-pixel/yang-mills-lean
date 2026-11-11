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

## What it does not say

Two cubes at lambda/alpha = 1 is not excluded here, yet the stored search there was
inconclusive: the true edge of the method is earlier than this bound. The bound applies to
the total-electric cutoff C <= 8 with floor 28/3 only. It is the finite-graph form of the
fixed-total-cutoff obstruction in SCALING_AND_OBSTRUCTIONS.md.
