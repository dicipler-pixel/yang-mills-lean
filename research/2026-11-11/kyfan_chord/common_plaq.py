# Shared exact tools for the one-plaquette Ky Fan chord (Green, 2026-11-11).
# Model (ledger open_tests_05 T1/T2, repo su3_character_certificate):
#   H(kappa, lam) = kappa*C2 + lam*(3 - Re chi_(1,0)) on L2(SU3)^Ad (class functions of the plaquette holonomy),
#   orthonormal character basis chi_(p,q); diag kappa*c(p,q)+3 lam, six neighbours -lam/2.
#   E_i(kappa, lam) = kappa * e_i(lam/kappa), e_i = levels of C2 + mu(3 - Re chi).
import sys
from fractions import Fraction as F
import numpy as np
import pathlib
HERE = pathlib.Path(__file__).resolve().parent
YM = str(HERE.parents[1] / 'yang_mills_2026_09_09')  # repo-relative: research/yang_mills_2026_09_09
for p in ('/scripts', '/cross_theorem/scripts'):
    sys.path.insert(0, YM + p)
import su3_character_certificate as su

def hfloat(n, kap, lam):
    ss = su.states(n); idx = {s: i for i, s in enumerate(ss)}
    h = np.zeros((len(ss),) * 2)
    for i, (p, q) in enumerate(ss):
        h[i, i] = kap * float(su.casimir(p, q)) + 3 * lam
        for t in su.neighbors(p, q):
            j = idx.get(t)
            if j is not None: h[i, j] = h[j, i] = -lam / 2
    return ss, h

def levels(kap, lam, n=70, k=3):
    return np.linalg.eigvalsh(hfloat(n, kap, lam)[1])[:k]

# ---- certified lower bounds (repo Schur verifier, exact outward interval LDL) ----
def lower_e01(mu, N, eps=F(1, 10**10)):
    """Return rationals (z0, z1) with e0(mu) >= z0 and e1(mu) >= z1 (e1 = 2nd eigenvalue, multiplicity counted).
    Certificate: Schur tail matrix K(z) has 0 (resp. <= 1) negative pivots => H - z has 0 (<= 1) eigenvalues < z."""
    mu = F(mu)
    w = np.linalg.eigvalsh(hfloat(N + 10, 1.0, float(mu))[1])
    z0 = F(w[0]).limit_denominator(10**13) - eps
    z1 = F(w[1]).limit_denominator(10**13) - eps
    n0, p0 = su.interval_inertia(N, mu, z0, schur=True)
    n1, p1 = su.interval_inertia(N, mu, z1, schur=True)
    assert n0 == 0, ('E0 lower failed', mu, n0)
    assert n1 <= 1, ('E1 lower failed', mu, n1)
    return z0, z1

def trial_vector(kap, lam, N, den=10**12):
    """Rational finite-support trial vector from the float ground state (any vector works; quality only)."""
    ss, h = hfloat(N, float(kap), float(lam))
    w, v = np.linalg.eigh(h); v0 = v[:, 0] * np.sign(v[0, 0])
    return ss, [F(round(x * den), den) for x in v0]

def affine_quotient(ss, v):
    """Exact (n, c, m) with <v,v>=n, <v,C2 v>=c, <v,(3-Re chi)v>=m in the FULL space.
    So E0(kappa, lam) <= (kappa*c + lam*m)/n for every kappa, lam >= 0 (min-max, v of finite support)."""
    idx = {s: i for i, s in enumerate(ss)}
    n = sum(x * x for x in v)
    c = sum(v[i] * v[i] * su.casimir(*s) for i, s in enumerate(ss))
    off = F(0)
    for i, s in enumerate(ss):
        if not v[i]: continue
        for t in su.neighbors(*s):
            j = idx.get(t)
            if j is not None: off += v[i] * v[j]
    m = 3 * n - off / 2
    return n, c, m
