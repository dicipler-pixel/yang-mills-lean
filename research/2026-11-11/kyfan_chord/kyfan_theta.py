# Certified Ky Fan chord gap bound on the two-square cell (repo 19-state certificate cell), chord in lam (alpha=1).
# H(lam) = E_el + lam W, W = 6 - Re Tr U - Re Tr V, affine in lam => S = E0+E1 concave in lam.
#   gap(lam) >= chord_lo(lam) - 2 E0_up(lam) on each chord [a,b].
# S_lo(node): E0 >= z0 (0 negative pivots), E1 >= z1 (<= 1 negative pivot) of the exact Schur form
#   K(z) = A - zG - lam^2 M/(d-z), d = s*43/3 + 2e (repo hidden-floor allocation, inner floor e certified by
#   repo interval_inertia). Node lam=0: exact electric spectrum, S(0) = 0 + 16/3.
# E0_up: exact rational Rayleigh quotients of fixed 19-state trial vectors (affine in lam, valid for all lam).
# Exact gap: float spin-network Galerkin solver sn_theta.py (K=4), reference only.
import json, pathlib, time
HERE_ = pathlib.Path(__file__).resolve().parent
from fractions import Fraction as F
import numpy as np
import common_theta as ct
import sn_theta as sn
t0 = time.time()

# ---- controls ----
z0, z1, s, d = ct.lower_S(F(1))
assert ct.certify_neg(F(1), z0 + F(1, 100), d[0]) >= 1, 'E0 control'
assert ct.certify_neg(F(1), z1 + F(1, 100), d[1]) >= 2, 'E1 control'
print('controls: shifts 1/100 above the certified E0, E1 lower bounds at lam=1 are rejected (neg pivots rise)')

# ---- reference levels ----
K = 3   # grid scans use K=3 (built here); table values use K=4 from theta_reference.json
states, Eel, Sop = sn.build(K)
REF = json.load(open(HERE_ / 'theta_reference.json'))
REF4 = {F(l).limit_denominator(100): v for l, v in zip(REF['lams'], REF['res']['4']['levels'])}
import functools
@functools.lru_cache(maxsize=None)
def exact(lam):
    if F(lam) in REF4: v = REF4[F(lam)]; return v[0], v[1]
    H = np.diag(Eel + 6 * float(lam)) - float(lam) * Sop
    w = np.linalg.eigvalsh((H + H.conj().T) / 2)[:2]; return w[0], w[1]
print(f'reference: K=4 levels at table points (theta_reference.json); K=3 ({len(states)} states) on scan grids ({time.time()-t0:.0f}s)', flush=True)

nodes_all = [F(k, 4) for k in range(1, 17)] + [F(1, 10)]
SL = {F(0): (F(0), F(16, 3), ('exact',), ('exact',))}
print('\nnode certificates  lam   E0 >= z0      E1 >= z1      s0,s1       d0,d1              exact E0     exact E1', flush=True)
for lam in sorted(nodes_all):
    SL[lam] = ct.lower_S(lam)
    z0, z1, s, d = SL[lam]; e0, e1 = exact(lam)
    print(f'                  {float(lam):5.2f} {float(z0):11.6f}  {float(z1):11.6f}  {str(s[0])+","+str(s[1]):11s} {float(d[0]):8.4f},{float(d[1]):8.4f}  {e0:11.6f} {e1:11.6f}', flush=True)
def S_lo(lam): z0, z1 = SL[F(lam)][:2]; return z0 + z1

tang = [F(k, 16) for k in range(0, 65)] + [F(1, 10)]
LINES = [ct.trial_line(t) for t in tang]
def E0_up(x): return min(al + be * x for al, be in LINES)

def bound(a, b, x):
    Sa, Sb = S_lo(a), S_lo(b)
    return Sa + (Sb - Sa) * (x - a) / (b - a) - 2 * E0_up(x)

def uniform_min(a, b):
    cand = {F(a), F(b)}
    for i in range(len(LINES)):
        for j in range(i + 1, len(LINES)):
            (a1, b1), (a2, b2) = LINES[i], LINES[j]
            if b1 != b2:
                x = (a2 - a1) / (b1 - b2)
                if a <= x <= b: cand.add(x)
    return min((bound(a, b, x), x) for x in cand)

designs = {
    'single [0,4]': [F(0), F(4)],
    'ledger nodes {0,0.1,0.5,1,2,3,4}': [F(0), F(1, 10), F(1, 2), F(1), F(2), F(3), F(4)],
    'nodes {0,0.5,1,2,3,4}': [F(0), F(1, 2), F(1), F(2), F(3), F(4)],
    'nodes every 1/4': [F(k, 4) for k in range(17)],
}
TAB = [F(1, 10), F(1, 4), F(1, 2), F(3, 4), F(1), F(3, 2), F(2), F(5, 2), F(3), F(7, 2), F(4)]
direct = {'1/10': 5.284, '1/2': 5.103, '1': 4.909, '2': 4.274, '3': 2.467, '4': 0.991}  # ledger item 1 (rerun json)
out = dict(model='two SU(3) squares sharing one link (theta graph 1,3,3), H = E_el + lam(6 - ReTrU - ReTrV), alpha=1',
           sector='vertex-gauge-invariant L2 of the seven-link graph, all spin networks (both C-parities)',
           reference='sn_theta.py float: K=4 at table points, K=3 on scan grids', nodes={str(k): [str(x) for x in v] for k, v in SL.items()}, designs={})
for name, nodes in designs.items():
    print(f'\n=== chord design: {name} ===')
    print('  lam    chord        certified gap >=   exact-chord (float)   exact gap   loss    (ledger direct 19-state cert)')
    rows = []
    for x in TAB:
        piece = next((a, b) for a, b in zip(nodes, nodes[1:]) if a <= x <= b)
        cb = bound(piece[0], piece[1], x); e0, e1 = exact(x); g = e1 - e0
        a_, b_ = piece; Sa = sum(exact(a_)); Sb = sum(exact(b_))
        xc = Sa + (Sb - Sa) * float((x - a_) / (b_ - a_)) - 2 * e0
        dk = direct.get(str(x), '')
        rows.append(dict(lam=str(x), chord=[str(piece[0]), str(piece[1])], certified=str(cb), certified_f=float(cb),
                         E0_up=float(E0_up(x)), exact_E0=e0, exact_gap=g, exact_chord_float=xc, loss_pct=100 * (1 - float(cb) / g)))
        print(f' {float(x):5.2f}  [{float(piece[0]):.2f},{float(piece[1]):.2f}]   {float(cb):12.6f}      {xc:12.6f}       {g:9.5f}  {100*(1-float(cb)/g):6.1f}%   {dk}')
    pieces = []
    for a, b in zip(nodes, nodes[1:]):
        mn, at = uniform_min(a, b)
        xs = np.linspace(float(a), float(b), 41)
        worst = min(float(bound(a, b, F(v).limit_denominator(10**6))) / np.diff(exact(F(v).limit_denominator(10**6)))[0] for v in xs)
        pieces.append(dict(a=str(a), b=str(b), certified_min=str(mn), certified_min_f=float(mn), at=float(at), worst_ratio=worst))
        print(f'   piece [{float(a):.2f},{float(b):.2f}]: certified gap >= {float(mn):.6f} for EVERY lam in it (min at {float(at):.4f}); worst cert/exact {worst:.3f}')
    out['designs'][name] = dict(nodes=[str(v) for v in nodes], table=rows, pieces=pieces)
# E0 upper-bound quality (19-state RR vs reference)
print('\nE0 upper bound quality:  lam   E0_up(19-state RR)   exact E0   excess')
for x in TAB:
    print(f'                        {float(x):5.2f}  {float(E0_up(x)):12.6f}  {exact(x)[0]:12.6f}  {float(E0_up(x))-exact(x)[0]:.2e}')
out['elapsed_s'] = time.time() - t0
json.dump(out, open(HERE_ / 'kyfan_theta.json', 'w'), indent=1, default=str)
print(f'\nelapsed {time.time()-t0:.0f}s')
