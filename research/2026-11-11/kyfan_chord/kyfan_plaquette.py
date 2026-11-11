# Certified Ky Fan chord gap bound, one SU(3) plaquette, lam = 8, chord in kappa (ledger item 3 / open_tests_05 T2).
#   S(kappa) = E0 + E1 is concave in kappa (H affine in kappa), so on [a,b]:
#   gap(kappa) = S - 2 E0 >= chord_lo(kappa) - 2 E0_up(kappa),
#   chord_lo: line through certified lower bounds S_lo(a) = a(z0+z1)(8/a), S_lo(b).
#   E0_up: exact rational Rayleigh quotients of finite-support trial vectors in the full space
#          (affine in kappa, so one vector bounds E0 at EVERY kappa; we take the min over several).
# Exact gap and the ledger's float chord are float references (N=70 dense, converged ~1e-12).
import json, pathlib, sys, time
HERE_ = pathlib.Path(__file__).resolve().parent
from fractions import Fraction as F
import numpy as np
import common_plaq as cp

LAM = F(8); N = 40
t0 = time.time()

# ---- controls: wrong shifts must be rejected by the same verifier ----
mu0 = F(16); z0, z1 = cp.lower_e01(mu0, N)
assert cp.su.interval_inertia(N, mu0, z0 + F(1, 1000), schur=True)[0] >= 1     # above E0: not a lower bound
assert cp.su.interval_inertia(N, mu0, z1 + F(1, 1000), schur=True)[0] >= 2     # above E1: count must reach 2
ss, v = cp.trial_vector(F(1, 2), LAM, N); n, c, m = cp.affine_quotient(ss, v)
q = (F(1, 2) * c + LAM * m) / n; zz = cp.lower_e01(LAM * 2, N)[0] / 2
assert zz <= q, 'quotient below a certified lower bound'   # exact consistency: E0_lo <= E0 <= quotient
print('E0(1/2) bracket width (certified):', float(q - zz))
print('controls: wrong E0/E1 lower shifts rejected at mu=16; trial quotient above E0')

# ---- sector check (float): charge conjugation parity of the lowest levels ----
ss70, h70 = cp.hfloat(70, 1.0, 8.0); w, V = np.linalg.eigh(h70); ix = {s: i for i, s in enumerate(ss70)}
perm = [ix[(q, p)] for (p, q) in ss70]
cpar = [float(V[perm, k] @ V[:, k]) for k in range(3)]
print('sector: class functions of the plaquette holonomy = full gauge-invariant space; C-parity of E0,E1,E2 at kappa=1:',
      [round(x, 6) for x in cpar])

cacheS = {}
def S_lo(k):
    k = F(k)
    if k not in cacheS:
        z0, z1 = cp.lower_e01(LAM / k, N); cacheS[k] = k * (z0 + z1)
    return cacheS[k]
cacheT = {}
def line(k):
    """exact affine upper bound on E0(kappa, 8) from the trial vector tuned at kappa=k: E0 <= alpha*kappa + beta"""
    k = F(k)
    if k not in cacheT:
        ss, v = cp.trial_vector(k, LAM, N); n, c, m = cp.affine_quotient(ss, v); cacheT[k] = (c / n, LAM * m / n)
    return cacheT[k]
def E0_up(kap, lines):
    return min(al * kap + be for al, be in lines)

import functools, scipy.linalg as sl
@functools.lru_cache(maxsize=None)
def exact(kap):
    h = cp.hfloat(64, float(kap), 8.0)[1]
    e = sl.eigh(h, eigvals_only=True, subset_by_index=[0, 1]); return e[0], e[1]

def chord_bound(a, b, kap, lines):
    Sa, Sb = S_lo(a), S_lo(b)
    ch = Sa + (Sb - Sa) * (kap - a) / (b - a)
    return ch - 2 * E0_up(kap, lines)

def float_chord(a, b, kap):  # ledger construction: exact endpoints, exact E0 (not a bound)
    Sa = sum(exact(a)); Sb = sum(exact(b)); e0, e1 = exact(kap)
    return Sa + (Sb - Sa) * (float(kap) - float(a)) / (float(b) - float(a)) - 2 * e0

def uniform_min(a, b, lines):
    """exact min over kappa in [a,b] of the certified piecewise-linear bound (convex PL: min at a vertex)."""
    cand = {F(a), F(b)}
    for i in range(len(lines)):
        for j in range(i + 1, len(lines)):
            (a1, b1), (a2, b2) = lines[i], lines[j]
            if a1 != a2:
                x = (b2 - b1) / (a1 - a2)
                if a <= x <= b: cand.add(x)
    vals = [(chord_bound(a, b, x, lines), x) for x in cand]
    return min(vals)

out = dict(model='one SU(3) plaquette, H = kappa C2 + lam(3 - Re chi), lam = 8, chord variable kappa',
           sector='L2(SU3)^Ad: all class functions of the plaquette holonomy (= whole gauge-invariant space, both C-parities)',
           N_schur=N, eps='1e-10')

# ---- A: the ledger's chord (0.5, 2) at the ledger's five points ----
print('\nA. ledger chord a=1/2, b=2 (pointwise; E0_up from the trial vector tuned at that kappa)')
print(' kappa  exact gap   ledger float chord   certified bound   cert/float-chord   cert/exact')
A = []
for ks in ('3/4', '1', '5/4', '3/2', '7/4'):
    k = F(ks); L = [line(k)]
    cb = chord_bound(F(1, 2), F(2), k, L); fc = float_chord(F(1, 2), F(2), k); e0, e1 = exact(k)
    A.append(dict(kappa=ks, exact_gap=e1 - e0, ledger_float_chord=fc, certified=str(cb), certified_f=float(cb),
                  E0_up=str(E0_up(k, L)), E0_exact=e0))
    print(f' {float(k):5.2f}  {e1-e0:9.5f}   {fc:12.5f}        {float(cb):12.8f}     {float(cb)/fc:9.7f}       {float(cb)/(e1-e0):7.4f}')
print(' S_lo(1/2) =', float(S_lo(F(1, 2))), ' exact', sum(exact(0.5)), '   S_lo(2) =', float(S_lo(F(2))), ' exact', sum(exact(2)))
out['A_ledger_chord'] = A

# ---- B: several single chords, uniform over [a,b] ----
print('\nB. single chords: certified for EVERY kappa in [a,b] (trial vectors at 9 tangent points)')
print('   a     b    certified min over [a,b] (at kappa)   worst cert/exact on 61-pt grid (float)   at kappa')
B = []
grid_ex = {}
for a, b in ((F(1, 2), F(2)), (F(3, 4), F(7, 4)), (F(1, 2), F(5, 4)), (F(5, 4), F(2)), (F(1, 2), F(1)), (F(1), F(3, 2)), (F(3, 2), F(2)),
             (F(1, 4), F(4))):
    tang = [a + (b - a) * F(i, 8) for i in range(9)]; L = [line(t) for t in tang]
    mn, at = uniform_min(a, b, L)
    worst = (9, None)
    for x in np.linspace(float(a), float(b), 61):
        xf = F(x).limit_denominator(10**6)
        e0, e1 = exact(xf); r = float(chord_bound(a, b, xf, L)) / (e1 - e0)
        worst = min(worst, (r, float(xf)))
    B.append(dict(a=str(a), b=str(b), certified_min=str(mn), certified_min_f=float(mn), at=str(at),
                  worst_ratio_float=worst[0], worst_at=worst[1]))
    print(f' {float(a):5.2f} {float(b):5.2f}   {float(mn):12.6f}  ({float(at):.4f})                 {worst[0]:8.4f}                        {worst[1]:.3f}')
out['B_single_chords'] = B

# ---- C: piecewise chord covers of [1/2, 2] ----
print('\nC. covers of [1/2,2] by K equal chords (uniform certified bound on the whole interval)')
print('  K   certified min gap on [1/2,2]   exact min gap   worst cert/exact (float, 61 pts)   worst loss')
C = []
emin = min(np.diff(exact(F(x).limit_denominator(10**6)))[0] for x in np.linspace(0.5, 2, 61))
for K in (1, 2, 3, 6, 12):
    nodes = [F(1, 2) + F(3, 2) * F(i, K) for i in range(K + 1)]
    mins = []; worst = 9
    pieces = []
    for a, b in zip(nodes, nodes[1:]):
        tang = [a + (b - a) * F(i, 4) for i in range(5)]; L = [line(t) for t in tang]
        mn, at = uniform_min(a, b, L); mins.append(mn); pieces.append((a, b, L))
    for x in np.linspace(0.5, 2, 61):
        xf = F(x).limit_denominator(10**6)
        a, b, L = next(p for p in pieces if p[0] <= xf <= p[1])
        e0, e1 = exact(xf); worst = min(worst, float(chord_bound(a, b, xf, L)) / (e1 - e0))
    C.append(dict(K=K, nodes=[str(x) for x in nodes], certified_min=str(min(mins)), certified_min_f=float(min(mins)),
                  worst_ratio_float=worst))
    print(f' {K:2d}          {float(min(mins)):10.6f}               {emin:9.5f}           {worst:8.4f}                 {100*(1-worst):5.1f}%')
out['C_covers'] = C
out['elapsed_s'] = time.time() - t0
json.dump(out, open(HERE_ / 'kyfan_plaquette.json', 'w'), indent=1, default=str)
print(f'\nelapsed {time.time()-t0:.1f}s')
