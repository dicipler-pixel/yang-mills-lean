# Exact tools for the two-square cell (repo 19-state certificate cell), Green 2026-11-11.
# H(lam) = E_el + lam*(6 - Re Tr U - Re Tr V) on the gauge-invariant space of the seven-link two-square graph, alpha=1.
# Retained 19-state exact quadratic forms from the repo: A(lam) = (E+6lam)G - lam S, coupling form lam^2 M, Gram G.
import sys
from fractions import Fraction as F
import numpy as np, scipy.linalg as sl
import pathlib
HERE = pathlib.Path(__file__).resolve().parent
YM = str(HERE.parents[1] / 'yang_mills_2026_09_09')  # repo-relative: research/yang_mills_2026_09_09
for p in ('/scripts', '/cross_theorem/scripts'):
    sys.path.insert(0, YM + p)
import two_plaquette_19 as t19
import two_plaquette_certificate as tp
import su3_character_certificate as su

G, S, S2, M = t19.matrices()
n19 = len(G)
E = t19.ENERGY
Gf = np.array(G, float); Sf = np.array(S, float); Mf = np.array(M, float); Ef = np.array([float(x) for x in E])

def A_exact(lam):
    return [[(E[i] + 6 * lam) * G[i][j] - lam * S[i][j] for j in range(n19)] for i in range(n19)]

# ---------- hidden floor d(s) = s*43/3 + 2e,  e certified single-loop floor of kappa C2 + lam(3-Re chi), kappa=7/2(1-s)
def single_floor_float(kap, lam, n=40):
    ss = su.states(n); idx = {s: i for i, s in enumerate(ss)}
    h = np.zeros((len(ss),) * 2)
    for i, (p, q) in enumerate(ss):
        h[i, i] = kap * float(su.casimir(p, q)) + 3 * lam
        for t in su.neighbors(p, q):
            j = idx.get(t)
            if j is not None: h[i, j] = h[j, i] = -lam / 2
    return np.linalg.eigvalsh(h)[0]

def certified_floor(lam, s, n=25):
    """exact d with the repo's inner certificate (same as two_plaquette_19.certify_row)."""
    lam, s = F(lam), F(s); kap = F(7, 2) * (1 - s)
    if lam == 0: return s * t19.TAIL, F(0)
    e = F(single_floor_float(float(kap), float(lam))).limit_denominator(10**9) - F(1, 10**8)
    assert e < kap * su.tail_floor(n)
    neg, ps = su.interval_inertia(n, lam / kap, e / kap, schur=True)
    assert neg == 0 and all(lo > 0 for lo, hi in ps), 'local floor not proved'
    return s * t19.TAIL + 2 * e, e

def kmat_float(lam, z, d):
    A = np.diag(Ef + 6 * lam) @ Gf - lam * Sf
    return A - z * Gf - lam * lam * Mf / (d - z)

def neg_float(lam, z, d):
    return int((np.linalg.eigvalsh(kmat_float(lam, z, d)) < 0).sum())

def best_z(lam, d, k, hi=None):
    """largest float z < d with neg(K(z)) <= k (bisection)."""
    lo = -1.0; hi = d - 1e-9 if hi is None else hi
    if neg_float(lam, hi, d) <= k: return hi
    for _ in range(80):
        mid = (lo + hi) / 2
        if neg_float(lam, mid, d) <= k: lo = mid
        else: hi = mid
    return lo

def certify_neg(lam, z, d):
    """exact count of negative LDL pivots of K(z) = A - zG - lam^2 M/(d-z) (repo exact_inertia)."""
    lam, z, d = F(lam), F(z), F(d)
    assert z < d
    A = A_exact(lam)
    K = [[A[i][j] - z * G[i][j] - lam * lam * M[i][j] / (d - z) for j in range(n19)] for i in range(n19)]
    return tp.exact_inertia(K)[0]

def lower_S(lam, s_grid=None):
    """certified (z0, z1, (s0, s1), (d0, d1)): E0 >= z0, E1 >= z1 (multiplicity counted), via Haynsworth + hidden
    floor. The two bounds are separate certificates, so each uses its own allocation s (best of a grid)."""
    lam = F(lam)
    if s_grid is None: s_grid = [F(k, 40) for k in range(10, 40)]
    fl = {}
    for s in s_grid:
        kap = 3.5 * (1 - float(s)); e = single_floor_float(kap, float(lam)) if lam else 0.0
        fl[s] = float(s) * 43 / 3 + 2 * e
    zs, ss, ds = [], [], []
    for k in (0, 1):
        sb = max(s_grid, key=lambda s: best_z(float(lam), fl[s], k))
        d, e = certified_floor(lam, sb)
        z = F(best_z(float(lam), float(d), k)).limit_denominator(10**9) - F(1, 10**8)
        assert certify_neg(lam, z, d) <= k, ('lower failed', lam, k)
        zs.append(z); ss.append(sb); ds.append(d)
    return zs[0], zs[1], tuple(ss), tuple(ds)

def trial_line(lam):
    """exact affine upper bound E0(x) <= al + be*x valid for all x, from the 19-state RR vector tuned at lam."""
    A = np.diag(Ef + 6 * float(lam)) @ Gf - float(lam) * Sf
    w, v = sl.eigh(A, Gf); v0 = v[:, 0] / np.abs(v[:, 0]).max()
    vq = [F(round(x * 10**12), 10**12) for x in v0]
    def qf(Mx): return sum(vq[i] * Mx[i][j] * vq[j] for i in range(n19) for j in range(n19))
    g = qf(G); eg = sum(vq[i] * E[i] * G[i][j] * vq[j] for i in range(n19) for j in range(n19)); sv = qf(S)
    return eg / g, (6 * g - sv) / g
