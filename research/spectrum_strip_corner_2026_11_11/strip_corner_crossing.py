# Close strip and corner in (5, 5.25] under link-dependent s (Spectrum, 2026-11-11).
#
# Test (varying_s/README.md): a cell is excluded when L(c) > t, with
#   L(c) = (g_lo(c+h, lam) - g_up(c, lam)) / h,   h = c/1000,   c = E/P,
#   t = 1 (strip, c = 10/3) and t = 10/9 (corner, c = 3)   [strip_settle.py, strip_lower.py].
# g_lo, g_up are certify_slopes.py's (repo interval_inertia, N = 24, exact integer intervals):
# loaded verbatim by the same exec(...) used in varying_s/lambda_scan.py.
#
# For each cell we find lam* where L crosses t, as a certified bracket [lam_lo, lam_hi]:
#   lam_hi: certified L_lower(lam_hi) > t                 -> excluded at lam_hi
#   lam_lo: certified upper bound on the h-secant  <= t   -> this secant test cannot exclude at lam_lo
# WindowWallMono.forward_secant_mono (e concave on [0,inf), a hypothesis there) says the true forward
# secant is nondecreasing in lam, so exclusion at lam_hi carries to every lam >= lam_hi.
# Floats only propose; every accept/reject decision below is exact Fraction / integer-interval arithmetic.
import sys, os, json, math
from fractions import Fraction as F
from pathlib import Path
HERE = Path(__file__).resolve().parent
VS = HERE.parent / 'window_wall_2026_11_10' / 'varying_s'
YM = os.environ.setdefault('YM_RESEARCH', str(HERE.parents[1] / 'research' / 'yang_mills_2026_09_09'))
sys.argv = ['x', '24']
exec(open(VS.parent / 'certify_slopes.py').read().split("# failure control")[0])   # N, EPS, efloat, E_bounds, g_lo, g_up

def L_lower(c, lam, h):   # certified lower bound on the forward secant (identical to lambda_scan.py for h=c/1000)
    return (g_lo(c + h, lam) - g_up(c, lam)) / h
def L_upper(c, lam, h):   # certified upper bound on the same forward secant
    return (g_up(c + h, lam) - g_lo(c, lam)) / h
def L_float(c, lam, h):
    c, h, lam = float(c), float(h), float(lam)
    return ((c + h) * efloat(N + 6, lam / (c + h)) - c * efloat(N + 6, lam / c)) / h

GRID = 10**6
rows = []; controls = []
def ctrl(name, should_fail_claim, holds):
    ok = (holds is False)
    controls.append(dict(control=name, claim=should_fail_claim, claim_holds=holds, rejected_as_required=ok))
    print(f'   control: {name}: claim holds = {holds} -> ' + ('REJECTED (ok)' if ok else 'ACCEPTED (CONTROL FAILED)'), flush=True)
    assert ok, name

# reuse certify_slopes' own endpoint controls
mu0 = F(5, 2); lo0, up0 = E_bounds(mu0)
ctrl('wrong E upper endpoint (E_lo - 1/1000) at mu=5/2 certified as upper bound', 'E(5/2) < E_lo - 1/1000',
     su.interval_inertia(N, mu0, lo0 - F(1, 1000), schur=False)[0] >= 1)
ctrl('wrong E lower endpoint (E_up + 1/1000) at mu=5/2 certified as lower bound', 'E(5/2) >= E_up + 1/1000',
     su.interval_inertia(N, mu0, up0 + F(1, 1000), schur=True)[0] == 0)

for name, E, P, t, hden in [('strip', 10, 3, F(1), 1000), ('corner', 9, 3, F(10, 9), 1000)]:
    # (a smaller-h variant, h = c/10^5, was tried and was too slow to bracket in this session; left open)
    c = F(E, P); h = c / hden
    EPS = F(1, 10**10) if hden == 1000 else F(1, 10**11)   # certify_slopes' EPS for h=c/1000; dcube_uniform's 1e-11 for small h
    cache.clear()
    print(f'{name}: c = {c}, t = {t}, h = c/{hden}', flush=True)
    # sanity: reproduce lambda_scan / exact_t values at 5 and 5.25 (h = c/1000 only)
    if hden == 1000:
        for l in ('5', '5.25'):
            print(f'   lam={l}: L_lower = {float(L_lower(c, F(l), h)):.6f}', flush=True)
    a, b = 5.0, 5.25
    assert L_float(c, a, h) < float(t) < L_float(c, b, h)
    for _ in range(60):
        m = (a + b) / 2
        if L_float(c, m, h) > float(t): b = m
        else: a = m
    lam_f = (a + b) / 2
    k = math.ceil(lam_f * GRID)
    # walk up until certified exclusion, down until certified non-exclusion
    while not L_lower(c, F(k, GRID), h) > t: k += 1
    j = k - 1
    while not L_upper(c, F(j, GRID), h) <= t: j -= 1
    lam_hi, lam_lo = F(k, GRID), F(j, GRID)
    Lh, Ll = L_lower(c, lam_hi, h), L_upper(c, lam_lo, h)
    print(f'   float crossing lam* ~ {lam_f:.9f}', flush=True)
    print(f'   EXCLUDED (certified) at lam = {lam_hi} = {float(lam_hi)}:  L_lower = {float(Lh):.10f} > t = {t}  (margin {float(Lh - t):.3e})', flush=True)
    print(f'   secant test cannot exclude at lam = {lam_lo} = {float(lam_lo)}:  L_upper = {float(Ll):.10f} <= t  (margin {float(t - Ll):.3e})', flush=True)
    # controls that must fail
    ctrl(f'{name} h=c/{hden}: exclusion at lam_lo={float(lam_lo)}', 'L_lower(lam_lo) > t', L_lower(c, lam_lo, h) > t)
    ctrl(f'{name} h=c/{hden}: exclusion at lam_hi with t raised by 1/1000', 'L_lower(lam_hi) > t + 1/1000', Lh > t + F(1, 1000))
    if name == 'strip':
        ctrl(f'strip h=c/{hden}: exclusion at lam_hi against the pre-vertex-rule upper t = 36/35', 'L_lower(lam_hi) > 36/35', Lh > F(36, 35))
    else:
        ctrl(f'corner h=c/{hden}: exclusion at lam_hi with the strip coefficient c = 10/3 swapped in against t = 10/9',
             'monotone in c fails? L_lower(10/3) > 10/9', L_lower(F(10, 3), lam_hi, F(10, 3) / hden) > t)
    rows.append(dict(cell=name, c=str(c), t=str(t), h=str(h), N=N, eps=str(EPS), lam_float=lam_f,
                     lam_hi=str(lam_hi), L_lower_at_lam_hi=str(Lh), L_lower_at_lam_hi_float=float(Lh),
                     lam_lo=str(lam_lo), L_upper_at_lam_lo=str(Ll), L_upper_at_lam_lo_float=float(Ll),
                     excluded_for_all_lam_ge=str(lam_hi)))
json.dump(dict(rows=rows, controls=controls,
               monotonicity='WindowWallMono.forward_secant_mono: forward secant nondecreasing in lam (e concave on [0,inf) is a hypothesis there)',
               scope='strong-coupling window-wall bookkeeping on finite cells; no continuum or mass-gap claim'),
          open(HERE / 'strip_corner_crossing.json', 'w'), indent=1)
print('all controls rejected as required')
