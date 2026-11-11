# Certified upper bounds on the window-wall slope W'(0) = 28/3 - sum_p c_p g'(c_p).
# g(kappa,lam) = kappa * E(lam/kappa), E(mu) = ground energy of C2 + mu(3 - Re chi).
# Forward secant (g concave in kappa):  g'(c) >= (g_lo(c+h) - g_up(c)) / h.
# g_lo: repo Schur verifier (interval_inertia, schur=True, zero negative pivots => E >= shift).
# g_up: Rayleigh-Ritz on the truncated block (one or more negative pivots => E < shift).
# All acceptance decisions are exact integer interval arithmetic from su3_character_certificate.py.
import sys, json
from fractions import Fraction as F
import numpy as np
import os
from pathlib import Path
YM = os.environ.get('YM_RESEARCH', str(Path(__file__).resolve().parents[2] / 'research' / 'yang_mills_2026_09_09'))
for p in ('/scripts', '/cross_theorem/scripts', '/cross_theorem/native'):
    sys.path.insert(0, YM + p)
import su3_character_certificate as su
import spatial_gauge as sg
import spatial_certificates as sc

N = int(sys.argv[1]) if len(sys.argv) > 1 else 24
EPS = F(1, 10**10)

def efloat(n, mu):
    ss = su.states(n); idx = {s: i for i, s in enumerate(ss)}
    h = np.zeros((len(ss),) * 2)
    for i, (p, q) in enumerate(ss):
        h[i, i] = float(su.casimir(p, q)) + 3 * mu
        for t in su.neighbors(p, q):
            j = idx.get(t)
            if j is not None: h[i, j] = h[j, i] = -mu / 2
    return np.linalg.eigvalsh(h)[0]

cache = {}
def E_bounds(mu):
    mu = F(mu)
    if mu in cache: return cache[mu]
    e = F(efloat(N + 6, float(mu))).limit_denominator(10**14)
    up, lo = e + EPS, e - EPS
    nu, _ = su.interval_inertia(N, mu, up, schur=False)
    nl, _ = su.interval_inertia(N, mu, lo, schur=True)
    assert nu >= 1, ('upper failed', mu)
    assert nl == 0, ('lower failed', mu)
    cache[mu] = (lo, up); return lo, up

def g_lo(k, lam): return k * E_bounds(lam / k)[0]
def g_up(k, lam): return k * E_bounds(lam / k)[1]

# failure control: a deliberately wrong shift must be rejected.
mu0 = F(5, 2); lo0, up0 = E_bounds(mu0)
bad_up = lo0 - F(1, 1000)   # below E: Rayleigh-Ritz must NOT certify it as an upper bound
bad_lo = up0 + F(1, 1000)   # above E: Schur must NOT certify it as a lower bound
assert su.interval_inertia(N, mu0, bad_up, schur=False)[0] == 0
assert su.interval_inertia(N, mu0, bad_lo, schur=True)[0] >= 1
print('controls rejected: wrong upper and wrong lower endpoint at mu=5/2')

cases = [('strip', '5'), ('corner', '5'), ('cube', '3'), ('double_cube', '2'), ('two', '10'),
         ('strip', '10'), ('corner', '10'), ('cube', '4'), ('strip', '4'), ('corner', '4')]
out = []
for name, lam_s in cases:
    lam = F(lam_s); coef = sc.allocation_coeffs(sg.model(name))
    tot = F(0)
    for c in coef:
        h = c / 1000
        sec = (g_lo(c + h, lam) - g_up(c, lam)) / h
        tot += c * sec
    bound = F(28, 3) - tot
    out.append(dict(model=name, lam=lam_s, faces=len(coef), coeffs=[str(c) for c in coef],
                    certified_sum_c_gprime_lower=float(tot), slope_upper=float(bound),
                    excluded=bool(bound <= 0)))
    print(f'{name:12s} lam={lam_s:>3s}  sum c g\' >= {float(tot):.6f}   W\'(0) <= {float(bound):+.6f}   '
          + ('EXCLUDED (certified)' if bound <= 0 else 'not excluded'))
json.dump(dict(cutoff=N, eps=str(EPS), rows=out), open(f'certify_slopes_N{N}.json', 'w'), indent=1)
