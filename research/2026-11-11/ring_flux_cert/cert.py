"""Certified bounds for the SU(3) periodic ring (Green, ring_flux_cert).

Lower bounds: exact Schur/Feshbach form bound with a sector-specific hidden floor d,
    K(z) = A_PP - z G_PP - lam^2 C / (d - z),   C = <B b_i, Q B b_j>,
  #neg K(z) <= k  ==>  H (in that sector) has at most k eigenvalues below z.
  #neg is certified by a float congruence V^T K V with rigorous a-priori rounding bounds and
  Gershgorin discs separated from 0 (Sylvester's law of inertia; V proven nonsingular).
Upper bounds: exact rational Rayleigh quotients of rational trial vectors supported in P.
"""
import sys, json, time, math
from fractions import Fraction as F
import numpy as np, scipy.linalg as sl
import su3rep as S, ring, ham, matrices
from pathlib import Path
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1] / 'yang_mills_2026_09_09/scripts'))  # in-repo copy (main 3422e89)
import su3_character_certificate as su   # repo interval_inertia, unchanged (main 3422e89)

U = 2.0**-53

# ---------------- one-plaquette local floor ----------------
def plaq_e0_float(mu, n=24):
    st = su.states(n); ix = {s: i for i, s in enumerate(st)}
    H = np.zeros((len(st), len(st)))
    for (p, q), i in ix.items():
        H[i, i] = float(su.casimir(p, q)) + 3*mu
        for t in su.neighbors(p, q):
            if t in ix: H[i, ix[t]] -= mu/2
    return np.linalg.eigvalsh(H)[0]

def plaq_e0_cert(mu):
    """Certified lower bound e0(C2 + mu(3 - Re chi)) >= s via repo interval_inertia (N=20, Schur tail)."""
    ef = plaq_e0_float(float(mu))
    s = F(math.floor((ef - 1e-6)*10**6), 10**6)
    cnt, _ = su.interval_inertia(20, F(mu), s, schur=True)
    assert cnt == 0, ('plaquette floor not certified', mu, s)
    cnt2, _ = su.interval_inertia(20, F(mu), s + F(1, 1000), schur=True)
    return s, ef, cnt2   # control: shift + 1/1000 must be rejected (cnt2 >= 1)

# ---------------- hidden floor ----------------
def hidden_floor(G, sector, cap, lam, Estar_extra=6):
    """d <= Q H Q on the sector's complement Q of P (configs with E > cap).
    H = [E - theta*Hor] + sum_p [theta C2(b_p) + theta C2(t_p) + lam(3 - Re tr U_p)].
    First bracket is diagonal in configurations: >= m_Q(theta) = min_{c in Q} (E - theta Hor).
    Each plaquette term is >= 2 theta e0(lam/(2 theta)) (exclusive links b_p, t_p; translation
    invariance of C2 + Perron-Frobenius: the ground state of C2 + mu(3 - Re tr g) on L^2(SU(3)) is
    a class function), so d = m_Q(theta) + 2 theta L e0_lo(lam/(2 theta))."""
    L = G['L']; mod = ham.Model(G)
    Estar = F(cap) + Estar_extra
    cf = ring.enumerate_configs(G, Estar, sector, emin=F(cap))
    EH = []
    for e, c in cf:
        cfg = tuple(c[l] for l in G['order'])
        EH.append((e, mod.hor(cfg)))
    best = None
    for k in range(1, 20):
        th = F(k, 20)
        mq = min([e - th*h for e, h in EH] + [(1 - th)*Estar])
        dfl = float(mq) + 2*float(th)*L*plaq_e0_float(float(lam/(2*th)))
        if best is None or dfl > best[0]: best = (dfl, th, mq)
    _, th, mq = best
    mu = F(lam)/(2*th)
    s, ef, ctrl = plaq_e0_cert(mu)
    d = mq + 2*th*L*s
    return dict(d=d, theta=th, mQ=mq, mu=mu, e0_lo=s, e0_float=ef, e0_ctrl_count=ctrl,
                Estar=Estar, nQconfigs_enumerated=len(cf),
                minE_Q=min(e for e, h in EH) if EH else None)

# ---------------- rigorous inertia count ----------------
def certified_negcount(Kf):
    """Kf: float matrix, entrywise correctly rounded from the exact rational K.
    Returns exact #neg(K) or None if the discs do not separate from 0."""
    n = Kf.shape[0]
    gam = n*U/(1 - n*U)
    w, V = np.linalg.eigh(Kf)
    W = Kf @ V
    M = V.T @ W
    aV = np.abs(V); aK = np.abs(Kf)
    R = aV.T @ (aK @ aV)
    Err = 1.01*((2*U + gam)*R + gam*(aV.T @ np.abs(W))) + 1e-280
    N = V.T @ V
    nerr = 1.01*gam*(aV.T @ aV)
    if np.max(np.sum(np.abs(N - np.eye(n)) + nerr, axis=1))*1.01 >= 1: return None
    c = np.diag(M).copy()
    rad = (np.sum(np.abs(M), axis=1) - np.abs(c) + np.sum(Err, axis=1))*1.01 + 1e-15*np.abs(c)
    if np.any(np.abs(c) <= rad): return None
    return int(np.sum(c < 0)), float(np.min(np.abs(c) - rad))

def exact_K(Mx, lam, z, d):
    lam = F(lam); z = F(z); d = F(d)
    coef = lam*lam/(d - z)
    keys = set(Mx['AE']) | set(Mx['AB']) | set(Mx['G']) | set(Mx['C'])
    n = Mx['n']; Kf = np.zeros((n, n))
    for k in keys:
        v = Mx['AE'].get(k, 0) + lam*Mx['AB'].get(k, 0) - z*Mx['G'].get(k, 0) - coef*Mx['C'].get(k, 0)
        Kf[k] = float(v)          # Fraction -> float is correctly rounded
    return Kf

def dense(X, n):
    A = np.zeros((n, n))
    for (i, j), v in X.items(): A[i, j] = float(v)
    return A

def threshold(Mf, lam, d, k):
    """Float: largest z < d with lambda_{k}(K(z)) >= 0 (k=0 lowest)."""
    G, AE, AB, C = Mf
    def ev(z):
        return np.linalg.eigvalsh(AE + lam*AB - z*G - lam*lam/(d - z)*C)[k]
    lo, hi = 0.0, d - 1e-9
    if ev(lo) < 0: return None
    if ev(hi) >= 0: return hi
    for _ in range(60):
        mid = (lo + hi)/2
        if ev(mid) >= 0: lo = mid
        else: hi = mid
    return lo

def rayleigh(Mx, Mf, lam, which=0):
    G, AE, AB, C = Mf
    w, v = sl.eigh(AE + lam*AB, G)
    x = v[:, which]; x = x/np.max(np.abs(x))
    xr = [F(int(round(t*2**40)), 2**40) for t in x]
    lamF = F(lam)
    num = F(0); den = F(0)
    for (i, j), g in Mx['G'].items():
        if xr[i] and xr[j]: den += xr[i]*g*xr[j]
    for (i, j), a in Mx['AE'].items():
        if xr[i] and xr[j]: num += xr[i]*a*xr[j]
    for (i, j), a in Mx['AB'].items():
        if xr[i] and xr[j]: num += lamF*xr[i]*a*xr[j]
    return num/den, float(w[which])

def certify_level(Mx, Mf, lam, d, k, step=F(1, 10**5)):
    zf = threshold(Mf, float(lam), float(d), k)
    if zf is None: return dict(ok=False, reason='K(0) already has too many negatives')
    z = F(math.floor(zf/float(step)), 1)*step - step
    r = certified_negcount(exact_K(Mx, lam, z, d))
    if r is None or r[0] > k:
        return dict(ok=False, z=z, zf=zf, reason=f'count {r}')
    zc = z + F(1, 1000)
    rc = certified_negcount(exact_K(Mx, lam, zc, d)) if zc < F(d) else None
    return dict(ok=True, z=z, zf=zf, count=r[0], margin=r[1], ctrl_z=zc,
                ctrl_count=None if rc is None else rc[0], ctrl_rejected=(rc is not None and rc[0] > k))
