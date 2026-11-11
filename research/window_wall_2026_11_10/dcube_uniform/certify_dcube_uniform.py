# Certified upper bound on the window-wall slope W'(0) for the double cube
# with the uniform (Jensen) split c_p = 20/11 on all 11 faces, at the
# exclusion endpoint lambda/alpha = 17347717/10^7 = 1.7347717 (alpha = 1).
#
# U = 28/3 - sum_p c_p (g_lo(c_p+h) - g_up(c_p))/h
#   is an upper bound on W'(0) by the forward secant (g concave in kappa).
# U <= 0  =>  excluded (WindowWallFinite).
#
# g(kappa, lam) = kappa * e(lam/kappa).  Endpoints of e are certified by the
# repo interval_inertia verifier (N=24, EPS=1e-11):
#   E_lo: Schur complete-tail matrix, zero negative pivots => E(mu) >= E_lo
#   E_up: retained matrix, >= 1 negative pivot (Rayleigh-Ritz) => E(mu) < E_up
#
# Interval coverage is not needed: WindowWallMono.forward_secant_mono says
# the true forward secant is nondecreasing in lambda (e concave on [0, inf)),
# so a certified exclusion at this coupling holds at every larger coupling
# for the same graph and allocation.
import os, sys, json
from pathlib import Path
from fractions import Fraction as F
import numpy as np

HERE = Path(__file__).resolve().parent
# repo root is three levels up: research/window_wall_2026_11_10/dcube_uniform/
YM = os.environ.get('YM_RESEARCH', str(HERE.parents[2] / 'research' / 'yang_mills_2026_09_09'))
for p in ('/scripts', '/cross_theorem/scripts', '/cross_theorem/native'):
    sys.path.insert(0, YM + p)
import su3_character_certificate as su

N = 24
EPS = F(1, 10**11)
C = F(20, 11)
P = 11
LAM = F(17347717, 10**7)
H = F(1, 10**5)

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
    e = F(efloat(N + 6, float(mu))).limit_denominator(10**15)
    up, lo = e + EPS, e - EPS
    nu, _ = su.interval_inertia(N, mu, up, schur=False)
    nl, _ = su.interval_inertia(N, mu, lo, schur=True)
    assert nu >= 1, ('upper failed', mu)
    assert nl == 0, ('lower failed', mu)
    cache[mu] = (lo, up); return lo, up

# failure control: a deliberately wrong shift must be rejected
mu0 = F(5, 2); lo0, up0 = E_bounds(mu0)
bad_up = lo0 - F(1, 1000)
bad_lo = up0 + F(1, 1000)
assert su.interval_inertia(N, mu0, bad_up, schur=False)[0] == 0
assert su.interval_inertia(N, mu0, bad_lo, schur=True)[0] >= 1
print('controls rejected: wrong upper and wrong lower endpoint at mu=5/2')

mu_c = LAM / C
mu_ch = LAM / (C + H)
E_lo_c, E_up_c = E_bounds(mu_c)
E_lo_ch, E_up_ch = E_bounds(mu_ch)
g_up_c = C * E_up_c
g_lo_ch = (C + H) * E_lo_ch
secant = (g_lo_ch - g_up_c) / H
tot = P * C * secant
U = F(28, 3) - tot
assert U <= 0, ('expected exclusion, got U =', U)

out = dict(
    N=N,
    eps=str(EPS),
    faces=P,
    coeffs='20/11 x 11',
    c=str(C),
    lam=str(LAM),
    lam_f=float(LAM),
    h=str(H),
    mu_at_c=str(mu_c),
    mu_at_c_plus_h=str(mu_ch),
    E_lo_at_c=str(E_lo_c),
    E_up_at_c=str(E_up_c),
    E_lo_at_c_plus_h=str(E_lo_ch),
    E_up_at_c_plus_h=str(E_up_ch),
    g_up_c=str(g_up_c),
    g_lo_c_plus_h=str(g_lo_ch),
    secant_lower=str(secant),
    certified_sum_c_gprime_lower=str(tot),
    slope_upper=str(U),
    slope_upper_float=float(U),
    excluded=bool(U <= 0),
    monotonicity=(
        'WindowWallMono.forward_secant_mono: the true forward secant '
        'g(c+h,lam)-g(c,lam) is nondecreasing in lam (e concave on [0,inf)). '
        'A certified U<=0 at this lam therefore excludes every larger lam '
        'for the same graph and allocation (alpha=1). Concavity of e is a hypothesis.'
    ),
)
json.dump(out, open(HERE / 'certify_dcube_uniform.json', 'w'), indent=1)
print(f'c = {C} x {P}  lam = {LAM} = {float(LAM)}  h = {H}')
print(f'mu(c)      = {mu_c}')
print(f'mu(c+h)    = {mu_ch}')
print(f'E_up(c)    = {E_up_c}')
print(f'E_lo(c+h)  = {E_lo_ch}')
print(f'g_up(c)    = {g_up_c}')
print(f'g_lo(c+h)  = {g_lo_ch}')
print(f'secant lo  = {secant}')
print(f'sum c L    = {tot}')
print(f'W\'(0) <= U = {U}  = {float(U):+.10e}')
print('EXCLUDED (certified)' if U <= 0 else 'not excluded')
print('monotonicity: WindowWallMono carries this exclusion to every larger lambda')
