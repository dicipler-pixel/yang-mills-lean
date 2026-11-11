# SCRIPT: WINDOW_WALL_CERTIFIED_02
"""Certified version of the window wall, exact integer-interval arithmetic only
for acceptance (floats only PROPOSE endpoints).

For each face p with allocation coefficient c_p and one-loop ground energy
g(kappa) of kappa*C2 + lam*(3 - Re chi):
  g_low(kappa): t with the complete-tail one-loop Schur matrix at mu = lam/kappa,
                shift t/kappa, having 0 negative pivots  ->  g(kappa) >= t
                (same test the repo uses for its local floors).
  g_up(kappa):  u with the finite retained matrix at shift u/kappa having >= 1
                negative pivot  ->  g(kappa) <= u   (Rayleigh-Ritz).
  forward secant, g concave:  g'_right(c) >= L = (g_low(c+h) - g_up(c)) / h.
  W'(0) <= 28/3 - sum_p c_p L_p.   If that is <= 0 the C<=8 complete-tail class
  has no certificate on that graph at that coupling, at any s.

KILL CONDITION: if a graph/coupling with a stored accepted target comes out
EXCLUDED, the chain is wrong.
'not excluded' proves nothing: it only means this bound does not reach.
"""
import sys, json
from fractions import Fraction as F
import numpy as np

REPO = sys.argv[1]
for sub in ('scripts', 'cross_theorem/scripts', 'cross_theorem/native'):
    sys.path.insert(0, REPO + '/research/yang_mills_2026_09_09/' + sub)
import spatial_gauge as sg
import spatial_certificates as sc
import su3_character_certificate as su
from targets import all_targets

N = 30
H = F(1, 1000)
st = su.states(N); idx = {s: i for i, s in enumerate(st)}
C2 = np.array([float(su.casimir(p, q)) for p, q in st])
ADJ = np.zeros((len(st), len(st)))
for (p, q), i in idx.items():
    for t in su.neighbors(p, q):
        j = idx.get(t)
        if j is not None: ADJ[i, j] = 1.0

def e0_float(mu):
    return float(np.linalg.eigvalsh(np.diag(C2 + 3 * mu) - (mu / 2) * ADJ)[0])

cache = {}
def bounds(kappa, lam):
    """certified (g_low, g_up) for g(kappa) = kappa * E0(lam/kappa)."""
    key = (kappa, lam)
    if key in cache: return cache[key]
    mu = lam / kappa
    e = e0_float(float(mu))
    lo = F(int(e * 10**9) - 20, 10**9)          # proposal below
    hi = F(int(e * 10**9) + 20, 10**9)          # proposal above
    assert lo < su.tail_floor(N)
    neg, piv = su.interval_inertia(N, mu, lo, schur=True)
    assert neg == 0 and all(a > 0 for a, b in piv), 'lower endpoint not certified'
    neg2, _ = su.interval_inertia(N, mu, hi, schur=False)
    assert neg2 >= 1, 'upper endpoint not certified'
    cache[key] = (kappa * lo, kappa * hi)
    return cache[key]

have = {(n, t['lambda']) for n, rows in all_targets().items() for t in rows}
rows = []; wrong = 0
print(f"{'graph':12s} {'lam':>5s} {'sum c_p L_p (certified lower)':>30s} {'28/3 - sum':>12s}  verdict   stored target")
for name in ('two', 'strip', 'corner', 'cube', 'double_cube'):
    m = sg.model(name); coef = sc.allocation_coeffs(m)
    for lam_s in ('1', '2', '3', '4', '5', '6', '8', '10'):
        lam = F(lam_s); tot = F(0)
        for c in coef:
            L = (bounds(c + H, lam)[0] - bounds(c, lam)[1]) / H
            tot += c * L
        margin = F(28, 3) - tot
        excluded = margin <= 0
        stored = (name, lam_s) in have
        if excluded and stored: wrong += 1
        rows.append(dict(model=name, lam=lam_s, certified_sum=str(tot), certified_sum_float=float(tot),
                         margin_float=float(margin), excluded=excluded, stored_target=stored))
        print(f"{name:12s} {lam_s:>5s} {float(tot):30.6f} {float(margin):12.6f}  {'EXCLUDED' if excluded else 'not excl.'}  {'yes' if stored else '-'}")
print('KILL: stored targets inside a certified-excluded cell =', wrong)
print('one-loop certificates used:', len(cache), ' cutoff N =', N, ' h =', H, ' grid 2^-192')
json.dump(dict(N=N, h=str(H), rows=rows, kill_violations=wrong), open(sys.argv[2], 'w'), indent=1)
