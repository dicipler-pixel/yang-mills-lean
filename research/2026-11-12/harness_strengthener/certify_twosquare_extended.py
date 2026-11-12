#!/usr/bin/env python3
# SCRIPT: CERTIFY_TWOSQUARE_EXTENDED
"""Schur-inertia gap certificates for the SU(3) two-square cell (theta graph, arms 1,3,3; alpha = 1) with a
retained space much larger than the 19 states:  P = ALL spin-network states with electric energy <= ECUT.

    H(lam) = E_el + lam (6 - Re Tr U - Re Tr V),      E_el = 3 c(b) + 3 c(c) + c(a).

What is exact (Python int / fractions.Fraction, no floats):
  * the sl(3) irreps (rescaled Gelfand-Tsetlin, rational matrices, each verified by its commutation relations),
  * the highest-weight (multiplicity) vectors, the intertwiners with the fundamental (each verified),
  * hence the Gram matrix G, the matrix S of Re Tr U + Re Tr V on P and from P to every outside state it reaches,
    A = (E + 6 lam) G - lam S_PP,   M = lam^2 S_PR G_R^-1 S_RP  ( = B B^dagger exactly ),
  * the hidden floor d = s c_+ + 2 e  (allocation bound; e certified by the repo one-plaquette interval_inertia),
  * the Rayleigh quotient r >= E0 and the inertia of K(z) = A - z G - M/(d - z).
The inertia count: K is rounded (error bound carried) to an integer matrix Kt, an integer unit upper triangular
matrix Xt is PROPOSED by a float LDL, Y = Xt^T Kt Xt is computed exactly (int64 limb products that cannot
overflow, recombined in Python ints) and every Gershgorin disc of Y, widened by the rounding bound, must avoid 0.
Xt is invertible, so Sylvester's law gives inertia(K) = inertia(Y) = signs of the diagonal of Y.
Floats are used only to PROPOSE: the trial vector, the transform Xt, the test energies.  They cannot make a
false certificate pass.  No floating-point eigenvalue enters any acceptance decision.

Run:  OMP_NUM_THREADS=1 python3 certify_twosquare_extended.py            (verifier; about 3 to 5 minutes)
      OMP_NUM_THREADS=1 python3 certify_twosquare_extended.py --propose  (re-derive the targets by floats; slow)
"""
import os
os.environ.setdefault('OMP_NUM_THREADS', '1'); os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
import sys, time, json, argparse, functools
from fractions import Fraction as F
from math import isqrt, gcd
from pathlib import Path
import numpy as np
import scipy.linalg as sl

HERE = Path(__file__).resolve().parent


def find_repo():
    cands = []
    if os.environ.get('YM_REPO'): cands.append(Path(os.environ['YM_REPO']))
    cands += [HERE.parents[2] if len(HERE.parents) > 2 else HERE, Path('/home/claude/ym-harness/work/strengthener')]
    for c in cands:
        if (c / 'research/yang_mills_2026_09_09/scripts/two_plaquette_19.py').exists(): return c
    raise SystemExit('repo not found: set YM_REPO to the yang-mills-lean checkout')


REPO = find_repo()
sys.path.insert(0, str(REPO / 'research/yang_mills_2026_09_09/scripts'))
sys.path.insert(0, str(REPO / 'paper/2026-09-08/su3'))
import su3_character_certificate as su          # repo: certified one-plaquette floors (interval_inertia)
import two_plaquette_19 as t19                  # repo: exact Haar 19-state matrices (cross-check only)

# ---------------------------------------------------------------------------------------------------------
# Targets (proposed by --propose; every number below is re-verified exactly, none is trusted).
#   d = s * c_plus + 2 * e,   e = certified ground-energy floor of  kappa C2 + lam (3 - Re chi),  kappa = 7(1-s)/2
# ---------------------------------------------------------------------------------------------------------
TARGETS = [
    {"lam": "3", "ECUT": 50, "s": "26/40", "N": 25, "e": "5885920/1000000", "z": "2072542/100000"},
    {"lam": "4", "ECUT": 50, "s": "26/40", "N": 25, "e": "7079980/1000000", "z": "2534913/100000"},
    {"lam": "6", "ECUT": 60, "s": "26/40", "N": 25, "e": "9078430/1000000", "z": "3382471/100000"},
    {"lam": "8", "ECUT": 60, "s": "32/40", "N": 25, "e": "8463301/1000000", "z": "4128192/100000"},
]
# ECUT = 250 float reference (research/2026-11-11/su3_twosquare/README.md):  E0, E1, gap
REF = {3: (15.891177631356, 20.725452127774, 4.834274496417), 4: (20.143917394545, 25.349263836105, 5.205346441560),
       6: (27.390845671288, 33.825363275736, 6.434517604448), 8: (33.489179627595, 41.292599746451, 7.803420118855)}
OLD19 = {3: '2.467', 4: '0.991', 6: 'none', 8: 'none'}     # 19-state certificates (kyfan_chord README)


# =========================================================================================================
#  exact rational spin-network build (no floats in this section)
# =========================================================================================================

FW = [(1, 0), (-1, 1), (0, -1)]


def cas(p, q): return F(p * p + q * q + p * q + 3 * p + 3 * q, 3)
def dim(p, q): return (p + 1) * (q + 1) * (p + q + 2) // 2


def fsqrt(x):
    """exact square root of a nonnegative rational, or raise."""
    x = F(x); a, b = isqrt(x.numerator), isqrt(x.denominator)
    if a * a != x.numerator or b * b != x.denominator: raise ArithmeticError('not a rational square')
    return F(a, b)


def addto(d, k, v):
    w = d.get(k, 0) + v
    if w: d[k] = w
    else: d.pop(k, None)


@functools.lru_cache(maxsize=None)
def irrep(p, q):
    m13, m23, m33 = p + q, q, 0
    pats = [(m12, m22, m11) for m12 in range(m23, m13 + 1) for m22 in range(m33, m23 + 1)
            for m11 in range(m22, m12 + 1)]
    idx = {t: i for i, t in enumerate(pats)}; n = len(pats)
    assert n == dim(p, q)
    l3 = [m13, m23 - 1, m33 - 2]
    up = [[] for _ in range(n)]            # up[i] = list of (j, r, which) : squared orthonormal entry of E_which
    for (m12, m22, m11), i in idx.items():
        if m11 + 1 <= m12:
            up[i].append((idx[(m12, m22, m11 + 1)], F((m12 - m11) * (m11 - m22 + 1)), 1))
        l2 = [m12, m22 - 1]; l1 = m11
        for ii, new in ((0, (m12 + 1, m22, m11)), (1, (m12, m22 + 1, m11))):
            if new not in idx: continue
            num = -(l2[ii] - l3[0]) * (l2[ii] - l3[1]) * (l2[ii] - l3[2]) * (l2[ii] - l1 + 1)
            jj = 1 - ii
            den = (l2[ii] - l2[jj]) * (l2[ii] - l2[jj] + 1)
            val = F(num, den)
            assert val >= 0
            if val > 0: up[i].append((idx[new], val, 2))
    W = []
    for (m12, m22, m11) in pats:
        e1 = m11; e2 = m12 + m22 - m11; e3 = m13 + m23 + m33 - m12 - m22
        W.append((e1 - e2, e2 - e3))
    top = W.index((p, q)); assert W.count((p, q)) == 1
    down = [[] for _ in range(n)]
    for i in range(n):
        for (j, r, w) in up[i]: down[j].append((i, r))
    N = [None] * n; N[top] = F(1); queue = [top]
    while queue:
        j = queue.pop()
        for (i, r) in down[j]:
            if N[i] is None: N[i] = N[j] * r; queue.append(i)
    assert all(x is not None and x > 0 for x in N)
    E = {1: [dict() for _ in range(n)], 2: [dict() for _ in range(n)]}
    Fm = {1: [dict() for _ in range(n)], 2: [dict() for _ in range(n)]}
    for i in range(n):
        for (j, r, w) in up[i]:
            e = fsqrt(r * N[i] / N[j])          # E e_i = ... + e * e_j
            E[w][i][j] = e
            Fm[w][j][i] = e * N[j] / N[i]       # adjoint with respect to D = diag(N)
    R = dict(n=n, W=W, top=top, D=N, E1=E[1], E2=E[2], F1=Fm[1], F2=Fm[2], pq=(p, q))
    verify_irrep(R)
    return R


def _mul(A, B, n):
    """operator product A o B for column-sparse operators (op[i] = image of e_i)."""
    out = [dict() for _ in range(n)]
    for i in range(n):
        for j, v in B[i].items():
            for k, w in A[j].items(): addto(out[i], k, v * w)
    return out


def _comm(A, B, n):
    X, Y = _mul(A, B, n), _mul(B, A, n)
    out = []
    for i in range(n):
        d = dict(X[i])
        for k, v in Y[i].items(): addto(d, k, -v)
        out.append(d)
    return out


def verify_irrep(R):
    """Exact proof that (E1,E2,F1,F2,D) is the irreducible sl(3) module of highest weight (p,q), unitary for D."""
    n, W, D = R['n'], R['W'], R['D']; p, q = R['pq']
    E1, E2, F1, F2 = R['E1'], R['E2'], R['F1'], R['F2']
    zero = [dict() for _ in range(n)]
    # weights: E1 raises by alpha1=(2,-1), E2 by alpha2=(-1,2), F lower
    for op, a in ((E1, (2, -1)), (E2, (-1, 2)), (F1, (-2, 1)), (F2, (1, -2))):
        for i in range(n):
            for j in op[i]: assert (W[j][0] - W[i][0], W[j][1] - W[i][1]) == a
    for k, (Ek, Fk) in enumerate(((E1, F1), (E2, F2))):
        C = _comm(Ek, Fk, n)
        assert C == [({i: F(W[i][k])} if W[i][k] else {}) for i in range(n)]
    assert _comm(E1, F2, n) == zero and _comm(E2, F1, n) == zero
    for X, Y in ((E1, E2), (E2, E1), (F1, F2), (F2, F1)):          # Serre relations
        assert _comm(X, _comm(X, Y, n), n) == zero
    for Ek, Fk in ((E1, F1), (E2, F2)):                              # F = adjoint of E for the form D
        for i in range(n):
            for j, v in Ek[i].items(): assert Fk[j][i] * D[i] == v * D[j]
        assert sum(len(x) for x in Ek) == sum(len(x) for x in Fk)
    hw = [i for i in range(n) if not E1[i] and not E2[i]]
    assert W[R['top']] == (p, q) and R['top'] in hw and n == dim(p, q)
    return True


# ---------------- sparse vectors in tensor products ----------------
def apply2(Rb, Rc, name, v):
    """action of a Lie algebra generator on V_b (x) V_c, vector = dict {(i,j): value}."""
    A, B = Rb[name], Rc[name]; out = {}
    for (i, j), x in v.items():
        for i2, c in A[i].items(): addto(out, (i2, j), x * c)
        for j2, c in B[j].items(): addto(out, (i, j2), x * c)
    return out


def nullspace(rows, ncols):
    """exact null space basis (list of length-ncols Fraction lists) of a list of sparse rows {col: value}."""
    piv = {}                                             # pivot col -> fully reduced row, leading coeff 1
    for r in rows:
        r = dict(r)
        while True:
            hit = [c for c in r if c in piv]
            if not hit: break
            for c in hit:
                f = r.get(c)
                if f:
                    for k, v in piv[c].items(): addto(r, k, -f * v)
        if not r: continue
        c = min(r); f = r[c]; r = {k: v / f for k, v in r.items()}
        for c2, pr in piv.items():
            g = pr.get(c)
            if g:
                for k, v in r.items(): addto(pr, k, -g * v)
        piv[c] = r
    for c, pr in piv.items():
        assert pr[c] == 1 and not any(c2 in piv for c2 in pr if c2 != c)
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    for f in free:
        x = [F(0)] * ncols; x[f] = F(1)
        for c, pr in piv.items():
            if f in pr: x[c] = -pr[f]
        basis.append(x)
    return basis


def hw_vectors(Rb, Rc, a):
    """rational basis of the highest-weight vectors of weight a in V_b (x) V_c, orthogonal for D_b (x) D_c.
    Returns list of (vector dict, norm)."""
    keys = [(i, j) for i in range(Rb['n']) for j in range(Rc['n'])
            if (Rb['W'][i][0] + Rc['W'][j][0], Rb['W'][i][1] + Rc['W'][j][1]) == tuple(a)]
    if not keys: return []
    col = {k: t for t, k in enumerate(keys)}
    rows = {}
    for name in ('E1', 'E2'):
        for k in keys:
            img = apply2(Rb, Rc, name, {k: F(1)})
            for tgt, v in img.items(): rows.setdefault((name, tgt), {})[col[k]] = v
    ns = nullspace(list(rows.values()), len(keys))
    Db, Dc = Rb['D'], Rc['D']
    vecs = []
    for x in ns:
        den = 1
        for y in x: den = den * y.denominator // gcd(den, y.denominator)
        v = {keys[t]: y * den for t, y in enumerate(x) if y}
        for (u, nu) in vecs:                                   # rational Gram-Schmidt (no normalisation)
            ip = sum(val * u.get(k, 0) * Db[k[0]] * Dc[k[1]] for k, val in v.items())
            if ip:
                f = ip / nu
                for k, val in u.items(): addto(v, k, -f * val)
        nv = sum(val * val * Db[k[0]] * Dc[k[1]] for k, val in v.items())
        assert nv > 0
        vecs.append((v, nv))
    for (v, nv) in vecs:                                        # exact re-check: highest weight
        assert not apply2(Rb, Rc, 'E1', v) and not apply2(Rb, Rc, 'E2', v)
    return vecs


def dominant_weights(Rb, Rc):
    s = set()
    for wb in set(Rb['W']):
        for wc in set(Rc['W']):
            w = (wb[0] + wc[0], wb[1] + wc[1])
            if w[0] >= 0 and w[1] >= 0: s.add(w)
    return sorted(s)


def racah_speiser(b, c):
    """multiplicities N_bc^a by the Racah-Speiser algorithm (integers only)."""
    out = {}
    for (x, y) in irrep(*b)['W']:
        l = [c[0] + x + 1, c[1] + y + 1]; s = 1
        for _ in range(12):
            if l[0] < 0: l = [-l[0], l[0] + l[1]]; s = -s; continue
            if l[1] < 0: l = [l[0] + l[1], -l[1]]; s = -s; continue
            break
        assert l[0] >= 0 and l[1] >= 0
        if l[0] == 0 or l[1] == 0: continue
        k = (l[0] - 1, l[1] - 1); out[k] = out.get(k, 0) + s
    out = {a: n for a, n in out.items() if n}
    assert all(n > 0 for n in out.values())
    assert sum(n * dim(*a) for a, n in out.items()) == dim(*b) * dim(*c)
    return out


RF = None
def fund():
    global RF
    if RF is None: RF = irrep(1, 0)
    return RF


@functools.lru_cache(maxsize=None)
def J_fund(b, b2):
    """exact intertwiner J : V_b2 -> V_b (x) V_f  (b2 = b + a weight of f).  Returns (cols, jnorm) where
    cols[i'] = dict {(i,m): value} and J*J = jnorm * identity.  The intertwining property is verified exactly."""
    Rb, Rf, R2 = irrep(*b), fund(), irrep(*b2)
    h = hw_vectors(Rb, Rf, b2); assert len(h) == 1
    n2 = R2['n']; cols = [None] * n2; cols[R2['top']] = h[0][0]
    W2 = R2['W']; top = W2[R2['top']]
    def depth(w):
        d0, d1 = top[0] - w[0], top[1] - w[1]            # = n1*(2,-1) + n2*(-1,2)
        n1 = F(2 * d0 + d1, 3); nn2 = F(d0 + 2 * d1, 3)
        assert n1.denominator == 1 and nn2.denominator == 1
        return int(n1 + nn2)
    byw = {}
    for i, w in enumerate(W2): byw.setdefault(w, []).append(i)
    for w in sorted(byw, key=depth):
        S = byw[w]
        if cols[S[0]] is not None: continue
        Cs, Ys = [], []
        for name, al in (('F1', (2, -1)), ('F2', (-1, 2))):
            wp = (w[0] + al[0], w[1] + al[1])
            for m in byw.get(wp, []):
                Cs.append([R2[name][m].get(i, F(0)) for i in S]); Ys.append(apply2(Rb, Rf, name, cols[m]))
        # solve  sum_i C[col][i] X_i = Y_col  exactly : X = Y C^T (C C^T)^-1  with C as |S| x ncol
        k = len(S); G = [[sum(Cs[t][i] * Cs[t][j] for t in range(len(Cs))) for j in range(k)] for i in range(k)]
        Gi = inv_small(G)
        for ii, i in enumerate(S):
            x = {}
            for t in range(len(Cs)):
                coef = sum(Cs[t][j] * Gi[j][ii] for j in range(k))
                if coef:
                    for key, v in Ys[t].items(): addto(x, key, coef * v)
            cols[i] = x
    # exact verification of the intertwining property for all four generators
    for name in ('E1', 'E2', 'F1', 'F2'):
        for i in range(n2):
            lhs = apply2(Rb, Rf, name, cols[i]); rhs = {}
            for j, v in R2[name][i].items():
                for key, x in cols[j].items(): addto(rhs, key, v * x)
            assert lhs == rhs, ('J not an intertwiner', b, b2)
    Db, Df = Rb['D'], Rf['D']
    jn = sum(v * v * Db[k[0]] * Df[k[1]] for k, v in cols[R2['top']].items()) / R2['D'][R2['top']]
    assert jn > 0
    return cols, jn


def inv_small(a):
    n = len(a); m = [list(r) + [F(int(i == j)) for j in range(n)] for i, r in enumerate(a)]
    for k in range(n):
        pv = next(i for i in range(k, n) if m[i][k]); m[k], m[pv] = m[pv], m[k]
        v = m[k][k]; m[k] = [x / v for x in m[k]]
        for i in range(n):
            if i != k and m[i][k]:
                v = m[i][k]; m[i] = [x - v * y for x, y in zip(m[i], m[k])]
    return [r[n:] for r in m]


WORDS = [(), ('F1',), ('F2',), ('F1', 'F2'), ('F2', 'F1')]       # word (X,Y) means X(Y(v))


@functools.lru_cache(maxsize=None)
def Kcoef(a, a2):
    """highest-weight vector of a2 in V_a (x) V_f as sum_m sum_w x[m][w] word_w(top_a) (x) f_m  (exact)."""
    Ra, Rf = irrep(*a), fund()
    cols, _ = J_fund(a, a2); h = cols[irrep(*a2)['top']]
    top = {Ra['top']: F(1)}
    def ap(name, v):
        out = {}
        for i, x in v.items():
            for j, c in Ra[name][i].items(): addto(out, j, x * c)
        return out
    wv = []
    for w in WORDS:
        v = top
        for L in reversed(w): v = ap(L, v)
        wv.append(v)
    x = [[F(0)] * len(WORDS) for _ in range(3)]
    for m in range(3):
        hm = {k[0]: v for k, v in h.items() if k[1] == m}
        if not hm: continue
        wt = Ra['W'][next(iter(hm))]
        cand = [t for t in range(len(WORDS)) if wv[t] and Ra['W'][next(iter(wv[t]))] == wt]
        # least squares, then exact residual check
        keys = sorted(set(hm) | {k for t in cand for k in wv[t]})
        A = [[wv[t].get(k, F(0)) for t in cand] for k in keys]; y = [hm.get(k, F(0)) for k in keys]
        # pick an independent subset of candidate words
        sel = []
        for t in range(len(cand)):
            trial = sel + [t]
            G = [[sum(A[r][i] * A[r][j] for r in range(len(keys))) for j in trial] for i in trial]
            try:
                inv_small(G); sel = trial
            except StopIteration:
                pass
        G = [[sum(A[r][i] * A[r][j] for r in range(len(keys))) for j in sel] for i in sel]
        rhs = [sum(A[r][i] * y[r] for r in range(len(keys))) for i in sel]
        Gi = inv_small(G); sol = [sum(Gi[i][j] * rhs[j] for j in range(len(sel))) for i in range(len(sel))]
        for r in range(len(keys)):
            assert sum(A[r][sel[i]] * sol[i] for i in range(len(sel))) == y[r], 'word expansion failed'
        for i, t in enumerate(sel): x[m][cand[t]] = sol[i]
    return x


def el(b, c, a): return 3 * cas(*b) + 3 * cas(*c) + cas(*a)


def fund_targets(b):
    return [(b[0] + dx, b[1] + dy) for dx, dy in FW if b[0] + dx >= 0 and b[1] + dy >= 0]


def reps_upto(bound):
    """all irreps (p,q) with 3*c(p,q) <= bound.  c is strictly increasing in p and in q, so a box search with a
    verified edge is exhaustive."""
    P = 0
    while 3 * cas(P, 0) <= bound: P += 1
    out = [(p, q) for p in range(P + 1) for q in range(P + 1) if 3 * cas(p, q) <= bound]
    assert all(max(p, q) < P for p, q in out)        # (P,0),(0,P) excluded, monotonicity excludes the rest
    return out


class Build:
    """Exact build for electric cutoff ECUT (a Fraction or int).
    P = all states with E_el <= ECUT;  R = all states outside P that Re Tr U + Re Tr V connects to P."""
    def __init__(self, ECUT, verbose=False):
        self.ECUT = ECUT = F(ECUT)
        # (a) exhaustive enumeration.  E >= 3c(b)+3c(c), so every state with E <= ECUT+X has 3c(b)+3c(c) <= ECUT+X.
        X = F(6)
        reps = reps_upto(ECUT + X)
        self.mult = {}
        cplus = None; P = []
        for b in reps:
            for c in reps:
                if 3 * cas(*b) + 3 * cas(*c) > ECUT + X: continue
                for a, n in sorted(racah_speiser(b, c).items()):
                    e = el(b, c, a)
                    if e <= ECUT:
                        self.mult[(b, c, a)] = n
                        P += [(b, c, a, k, l) for k in range(n) for l in range(n)]
                    elif cplus is None or e < cplus: cplus = e
        assert cplus is not None and cplus <= ECUT + X, 'enlarge X'
        self.cplus = cplus                      # smallest omitted electric energy, over the WHOLE complement
        P.sort(key=lambda s: (el(*s[:3]), s))
        self.P = P; self.nP = len(P)
        self.index = {s: i for i, s in enumerate(P)}
        self.states = list(P)
        self.hw = {}
        self.Tf = {'U': {}, 'V': {}}            # form matrices of multiplication by chi_f(U) and by chi_f(V)
        self._build(verbose)

    def inP(self, b, c, a): return (b, c, a) in self.mult

    def get_hw(self, b, c, a):
        key = (b, c, a)
        if key not in self.hw:
            v = hw_vectors(irrep(*b), irrep(*c), a)
            assert len(v) == racah_speiser(b, c).get(a, 0), 'multiplicity mismatch'
            self.hw[key] = v
        return self.hw[key]

    def idx(self, s):
        i = self.index.get(s)
        if i is None:
            i = len(self.states); self.index[s] = i; self.states.append(s)
        return i

    def _build(self, verbose):
        Pblocks = sorted({(s[0], s[1]) for s in self.P})
        pairs = set()
        for (b, c) in Pblocks:
            for b2 in fund_targets(b): pairs.add(('U', b, c, b2))        # source in P-block
            for c2 in fund_targets(c): pairs.add(('V', b, c, c2))
            for dx, dy in FW:                                             # target in P-block
                b0 = (b[0] - dx, b[1] - dy)
                if min(b0) >= 0: pairs.add(('U', b0, c, b))
                c0 = (c[0] - dx, c[1] - dy)
                if min(c0) >= 0: pairs.add(('V', b, c0, c))
        self.npairs = len(pairs)
        for t, pr in enumerate(sorted(pairs)):
            self._pair(*pr)
        self.nAll = len(self.states)

    def _pair(self, move, b, c, arm2):
        Rb, Rc, Rf = irrep(*b), irrep(*c), fund()
        arm = b if move == 'U' else c
        tb, tc = (arm2, c) if move == 'U' else (b, arm2)
        src = racah_speiser(b, c); tgt = racah_speiser(tb, tc)
        need = [(a, a2) for a in src for a2 in fund_targets(a) if a2 in tgt
                and (self.inP(b, c, a) or self.inP(tb, tc, a2))]
        if not need: return
        Jc, jn = J_fund(arm, arm2)
        Db, Dc, Df = Rb['D'], Rc['D'], Rf['D']
        Rtb, Rtc = irrep(*tb), irrep(*tc)
        # J w' for the needed target hw vectors, as dict {(i,j,m): value} in V_b (x) V_c (x) V_f
        Jw = {}
        for a2 in sorted({x[1] for x in need}):
            lst = []
            for (w, nw) in self.get_hw(tb, tc, a2):
                u = {}
                if move == 'U':
                    for (i2, j), x in w.items():
                        for (i, m), y in Jc[i2].items(): addto(u, (i, j, m), x * y)
                else:
                    for (i, j2), x in w.items():
                        for (j, m), y in Jc[j2].items(): addto(u, (i, j, m), x * y)
                lst.append(u)
            Jw[a2] = lst
        wordcache = {}
        for (a, a2) in sorted(need):
            hs = self.get_hw(b, c, a); ht = self.get_hw(tb, tc, a2)
            x = Kcoef(a, a2)
            Kv = []
            for k, (w, nw) in enumerate(hs):
                if (a, k) not in wordcache:
                    wl = []
                    for wd in WORDS:
                        v = w
                        for L in reversed(wd): v = apply2(Rb, Rc, L, v)
                        wl.append(v)
                    wordcache[(a, k)] = wl
                wl = wordcache[(a, k)]; u = {}
                for m in range(3):
                    for t in range(len(WORDS)):
                        if x[m][t]:
                            for (i, j), val in wl[t].items(): addto(u, (i, j, m), x[m][t] * val)
                Kv.append(u)
            NK = [sum(v * v * Db[k[0]] * Dc[k[1]] * Df[k[2]] for k, v in u.items()) for u in Kv]
            assert all(z > 0 for z in NK)
            R = [[sum(v * u2.get(k, 0) * Db[k[0]] * Dc[k[1]] * Df[k[2]] for k, v in u.items()) for u2 in Jw[a2]]
                 for u in Kv]
            Na, N2 = len(hs), len(ht)
            pref = F(dim(*a2), dim(*tb) * dim(*tc)) / jn
            srcP, tgtP = self.inP(b, c, a), self.inP(tb, tc, a2)
            for k in range(Na):
                for l in range(Na):
                    for k2 in range(N2):
                        for l2 in range(N2):
                            v = pref * R[l][l2] * R[k][k2] / (NK[l] * ht[l2][1])
                            if v:
                                r_ = self.idx((tb, tc, a2, k2, l2)); c_ = self.idx((b, c, a, k, l))
                                assert (r_, c_) not in self.Tf[move]
                                self.Tf[move][(r_, c_)] = v

    def gram(self):
        """diagonal Gram of the basis functions tr(Phi_{a,k,l} D^b(U) (x) D^c(V))."""
        G = []
        for (b, c, a, k, l) in self.states:
            h = self.get_hw(b, c, a)
            G.append(h[k][1] / h[l][1] * F(dim(*a), dim(*b) * dim(*c)))
        return G

    def energies(self): return [el(*s[:3]) for s in self.states]

    def S_form(self):
        """form matrix of Re Tr U + Re Tr V = (T + T^dagger)/2, as dict {(i,j): value}, symmetric, entries with
        at least one index in P."""
        S = {}
        for mv in 'UV':
            for (r, c), v in self.Tf[mv].items():
                addto(S, (r, c), v / 2); addto(S, (c, r), v / 2)
        return S


# =========================================================================================================
#  exact matrices on P and the coupling Gram
# =========================================================================================================
class Cell:
    def __init__(self, ECUT):
        t = time.time()
        self.B = B = Build(ECUT); self.n = n = B.nP
        self.G = B.gram(); self.E = B.energies(); self.cplus = B.cplus
        S = B.S_form()
        self.Spp = {}; out = {}
        for (i, j), v in S.items():
            if i < n and j < n: self.Spp[(i, j)] = v
            elif i < n: out.setdefault(j, []).append((i, v))
            else: assert j < n, 'entry with both ends outside P'
        # M0 = S_PR G_R^-1 S_RP  (form of P S Q S P; B B^dagger = lam^2 * M0)
        M0 = {}
        for r, lst in out.items():
            g = self.G[r]
            for (i, v) in lst:
                for (j, w) in lst: addto(M0, (i, j), v * w / g)
        self.M0 = M0; self.nR = len(out)
        self.boundary = len({i for (i, j) in M0})
        self.build_seconds = time.time() - t

    def floats(self):
        n = self.n; g = np.array([float(x) for x in self.G[:n]]); sg = np.sqrt(g)
        Sf = np.zeros((n, n)); Mf = np.zeros((n, n))
        for (i, j), v in self.Spp.items(): Sf[i, j] = float(v) / (sg[i] * sg[j])
        for (i, j), v in self.M0.items(): Mf[i, j] = float(v) / (sg[i] * sg[j])
        return np.array([float(e) for e in self.E[:n]]), sg, Sf, Mf

    def K(self, lam, z, d):
        """exact K(z) = A - z G - lam^2 M0/(d - z) as a dict of Fractions (form matrix in the rational basis)."""
        assert z < d
        f = -lam * lam / (d - z); K = {k: f * v for k, v in self.M0.items()}
        for k, v in self.Spp.items(): addto(K, k, -lam * v)
        for i in range(self.n): addto(K, (i, i), (self.E[i] + 6 * lam - z) * self.G[i])
        return K

    def rayleigh(self, lam, x):
        """exact Rayleigh quotient of the integer vector x (rational basis) for A = (E + 6 lam) G - lam S_PP."""
        n = self.n
        num = sum((self.E[i] + 6 * lam) * self.G[i] * x[i] * x[i] for i in range(n) if x[i])
        num -= lam * sum(v * x[i] * x[j] for (i, j), v in self.Spp.items() if x[i] and x[j])
        den = sum(self.G[i] * x[i] * x[i] for i in range(n) if x[i])
        assert den > 0
        return num / den


# =========================================================================================================
#  exact inertia:  integer congruence + Gershgorin
# =========================================================================================================
LB = 26; LH = 1 << (LB - 1); LMASK = (1 << LB) - 1


def limbs(x):
    """balanced base-2^26 digits of an object array of Python ints: x = sum_k L[k] * 2^(26k), |L[k]| <= 2^25."""
    out = []; x = x.copy()
    while True:
        r = ((x + LH) & LMASK) - LH
        out.append(r.astype(np.int64)); x = (x - r) >> LB
        if not x.any(): return out


def exact_matmul(A, B):
    """exact product of two integer matrices given as limb lists (int64).  Each int64 product entry is bounded by
    n * 2^50 < 2^63, so no wrap-around can occur; sums are taken in Python ints."""
    n = A[0].shape[1]; assert n * (1 << 50) < (1 << 63)
    acc = {}
    for i, a in enumerate(A):
        for j, b in enumerate(B):
            p = (a @ b).astype(object)
            acc[i + j] = p if i + j not in acc else acc[i + j] + p
    tot = None
    for k, v in acc.items():
        v = v << (LB * k); tot = v if tot is None else tot + v
    return tot


def certified_inertia(K, n, Q=52, PX=40, MS=30):
    """K: dict {(i,j): Fraction}, exactly symmetric, n x n.  Returns (number of negative eigenvalues, n, info) with
    proof, or raises ArithmeticError when the Gershgorin test is not conclusive.

    Proof.  Sc = diag(sc_i / 2^MS) > 0 rational and K' = 2^Q Sc K Sc.  Kt = round(K') entrywise, |K' - Kt| <= 1/2.
    Xt integer, upper triangular with diagonal 2^PX > 0, hence invertible.  Y = Xt^T Kt Xt exactly.  Then
    Xt^T K' Xt = Y + Err with |Err_ij| <= c_i c_j / 2, c_i = sum_k |Xt_ki|.  If |Y_ii| > sum_{j != i} |Y_ij| +
    c_i * sum_j c_j / 2 for every i, every Gershgorin disc of the symmetric matrix Xt^T K' Xt avoids 0, and by
    Sylvester inertia(K) = inertia(K') = inertia(Xt^T K' Xt) = signs of diag(Y)."""
    for (i, j), v in K.items(): assert K.get((j, i)) == v
    order = list(range(n - 1, -1, -1))                     # high electric energy first (stable elimination order)
    pos = {s: t for t, s in enumerate(order)}
    sc = [0] * n
    for i in range(n):
        kii = abs(float(K.get((i, i), 0)))
        sc[i] = max(1, int(round((1 << MS) / np.sqrt(kii)))) if kii > 0 else 1 << MS
    Kt = np.zeros((n, n), dtype=object); Kt[:, :] = 0
    den_shift = 2 * MS
    for (i, j), v in K.items():
        t = v.numerator * sc[i] * sc[j] << Q; dd = v.denominator << den_shift
        Kt[pos[i], pos[j]] = (2 * t + dd) // (2 * dd)        # nearest integer, error <= 1/2
    assert (Kt == Kt.T).all()
    Kf = Kt.astype(float) / float(1 << Q)
    # float LDL without pivoting: only a proposal for Xt
    A = Kf.copy(); L = np.eye(n)
    for k in range(n - 1):
        dk = A[k, k]
        if dk == 0 or not np.isfinite(dk): raise ArithmeticError('float proposal broke down')
        col = A[k + 1:, k].copy(); l = col / dk; L[k + 1:, k] = l
        A[k + 1:, k + 1:] -= np.outer(l, col)
    X = sl.solve_triangular(L, np.eye(n), lower=True, unit_diagonal=True).T       # X = L^-T, unit upper triangular
    if not np.isfinite(X).all() or np.abs(X).max() >= 2.0 ** 20: raise ArithmeticError('transform too large')
    Xi = np.triu(np.rint(X * float(1 << PX)).astype(np.int64), 1).astype(object)
    for i in range(n): Xi[i, i] = 1 << PX
    Kl = limbs(Kt); Xl = limbs(Xi); Xtl = [x.T.copy() for x in Xl]
    KX = exact_matmul(Kl, Xl)
    Y = exact_matmul(Xtl, limbs(KX))
    assert (Y == Y.T).all()
    absY = abs(Y); c = abs(Xi).sum(axis=0); ctot = int(c.sum())
    neg = 0; worst = None
    for i in range(n):
        dia = int(absY[i, i]); rad = int(absY[i].sum()) - dia + (int(c[i]) * ctot + 1) // 2
        if dia <= rad: raise ArithmeticError('Gershgorin disc %d contains zero: not certified' % i)
        neg += int(Y[i, i] < 0)
        ratio = rad / dia
        if worst is None or ratio > worst: worst = ratio
    return neg, n, dict(worst_radius_over_centre=float(worst), limbs_K=len(Kl), limbs_X=len(Xl))


# =========================================================================================================
#  hidden floor
# =========================================================================================================
def certified_floor(lam, s, e, N, cplus):
    """d = s c_+ + 2 e with e a certified lower bound of the one-plaquette ground energy at kappa = 7(1-s)/2."""
    assert 0 < s < 1 and isinstance(N, int) and N >= 1
    kap = F(7, 2) * (1 - s)
    if not e < kap * su.tail_floor(N): raise ArithmeticError('inner energy above its tail')
    neg, piv = su.interval_inertia(N, lam / kap, e / kap, schur=True)
    if neg != 0 or any(lo <= 0 for lo, hi in piv): raise ArithmeticError('one-plaquette floor not proved')
    return s * cplus + 2 * e, kap, len(piv)


def one_plaquette_float(lam, kap, N=25):
    ss = [(p, t - p) for t in range(N + 1) for p in range(t + 1)]; ix = {x: i for i, x in enumerate(ss)}
    H = np.zeros((len(ss),) * 2)
    for i, (p, q) in enumerate(ss):
        H[i, i] = kap * float(cas(p, q)) + 3 * lam
        for t in ((p + 1, q), (p - 1, q + 1), (p, q - 1), (p, q + 1), (p + 1, q - 1), (p - 1, q)):
            if t in ix: H[i, ix[t]] = -lam / 2
    return np.linalg.eigvalsh(H)[0]


# =========================================================================================================
#  exact cross-checks of the build
# =========================================================================================================
def check_against_repo19():
    """ECUT = 40/3: the new exact (E, G, S, M) and the repo's exact Haar (ENERGY, Gram, S, M) of the 19 states must
    have equal traces of ALL words of length <= 4 in the three operators E, G^-1 S, G^-1 M (exact rationals)."""
    C = Cell(F(40, 3)); n = C.n; assert n == 19 and C.cplus == F(43, 3) == t19.TAIL
    def dense(d, G): return [[d.get((i, j), F(0)) / G[i] for j in range(n)] for i in range(n)]
    mine = [[[C.E[i] if i == j else F(0) for j in range(n)] for i in range(n)], dense(C.Spp, C.G), dense(C.M0, C.G)]
    g, s, s2, m = t19.matrices(); gd = t19.GRAM_DIAG
    repo = [[[t19.ENERGY[i] if i == j else F(0) for j in range(n)] for i in range(n)],
            [[s[i][j] / gd[i] for j in range(n)] for i in range(n)], [[m[i][j] / gd[i] for j in range(n)] for i in range(n)]]
    def mm(a, b): return [[sum(a[i][k] * b[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
    def tr(a): return sum(a[i][i] for i in range(n))
    count = 0
    def rec(pm, pr, depth):
        nonlocal count
        for t in range(3):
            a = mm(pm, mine[t]) if pm else mine[t]; b = mm(pr, repo[t]) if pr else repo[t]
            if tr(a) != tr(b): raise AssertionError('19-state cross-check failed')
            count += 1
            if depth < 4: rec(a, b, depth + 1)
    rec(None, None, 1)
    return count


def check_structure(C):
    """exact identities on the built operators (columns are complete for sources in P):
       multiplication operators commute: [T_U, T_V] = 0, [T_U, T_U^dagger] = 0, [T_U, T_V^dagger] = 0,
       [T_V, T_V^dagger] = 0 on every state of P all of whose first images stay in P;
       on the one-plaquette (character) sector the coefficients are 1."""
    B = C.B; n = C.n; G = C.G
    col = {}
    for mv in 'UV':
        t = {}; td = {}
        for (r, c), v in B.Tf[mv].items():
            if c < n: t.setdefault(c, {})[r] = v / G[r]           # T column of source c
            if r < n: td.setdefault(r, {})[c] = v / G[c]          # T^dagger column of source r
        col[mv] = t; col[mv + 'd'] = td
    def compose(x, y, i):                                          # X Y e_i, or None if not computable inside P
        v = col[y].get(i, {})
        if any(k >= n for k in v): return None
        out = {}
        for k, a in v.items():
            for k2, b in col[x].get(k, {}).items(): addto(out, k2, a * b)
        return out
    tested = 0
    for x, y in (('U', 'V'), ('U', 'Ud'), ('U', 'Vd'), ('V', 'Vd')):
        for i in range(n):
            p, q = compose(x, y, i), compose(y, x, i)
            if p is None or q is None: continue
            if p != q: raise AssertionError('commutation check failed')
            tested += 1
    chars = 0
    for i, (b, c, a, k, l) in enumerate(B.states[:n]):
        if c == (0, 0):
            for b2 in fund_targets(b):
                j = B.index.get((b2, (0, 0), b2, 0, 0))
                if j is not None:
                    if B.Tf['U'].get((j, i), 0) / G[j] != 1: raise AssertionError('character rule failed')
                    chars += 1
    # normality on EVERY state of P, boundary included: |T Phi|^2 = |T^dagger Phi|^2.  The left side uses the
    # complete outgoing column (targets outside P included), the right side the complete incoming row.
    bal = 0
    for mv in 'UV':
        a = [F(0)] * n; b = [F(0)] * n
        for (r, c), v in B.Tf[mv].items():
            if c < n: a[c] += v * v / G[r]
            if r < n: b[r] += v * v / G[c]
        if a != b: raise AssertionError('norm balance failed')
        bal += n
    return tested, chars, bal


def check_method():
    """the integer congruence + Gershgorin count must agree with the repo's exact rational LDL (exact_inertia) on
    the new 19-state matrices, at the repo's own lambda = 1 and lambda = 4 targets and at shifted energies."""
    C = Cell(F(40, 3)); n = C.n; cnt = 0
    rows = {t['lambda']: t for t in json.loads((REPO / 'research/yang_mills_2026_09_09/scripts/'
                                                'two_plaquette_19_targets.json').read_text())}
    for lam in ('1', '4'):
        t = rows[lam]; d = F(t['d']); z0 = F(t['z'])
        for z in (F(t['r']), z0, z0 + F(3, 2), z0 + 3):
            if not z < d: continue
            K = C.K(F(lam), z, d)
            dense = [[K.get((i, j), F(0)) for j in range(n)] for i in range(n)]
            a = t19.tp.exact_inertia(dense)[0]; b = certified_inertia(K, n)[0]
            if a != b: raise AssertionError('inertia methods disagree')
            if z == z0 and a != 1: raise AssertionError('repo 19-state target not reproduced')
            cnt += 1
    return cnt


# =========================================================================================================
#  one coupling
# =========================================================================================================
def trial_and_levels(C, lam):
    E, sg, Sf, Mf = C.floats(); n = C.n
    A = np.diag(E + 6 * lam) - lam * Sf
    w, v = sl.eigh(A, subset_by_index=[0, 1])
    u = v[:, 0] / sg; u = u / np.abs(u).max()
    x = [int(t) for t in np.rint(u * float(1 << 40))]
    return w, x, (A, Mf)


def run_target(C, T):
    lam = F(T['lam']); s = F(T['s']); e = F(T['e']); z = F(T['z']); N = T['N']; li = int(lam)
    rec = dict(lam=T['lam'], ECUT=str(C.B.ECUT), n=C.n, hidden_reached=C.nR, boundary_states=C.boundary,
               c_plus=str(C.cplus), s=T['s'], e=T['e'], z=T['z'], status='FAILED')
    t0 = time.time()
    try:
        d, kap, npiv = certified_floor(lam, s, e, N, C.cplus)                       # (b)
        rec.update(d=str(d), d_float=float(d), kappa=str(kap), floor_pivots=npiv)
        w, x, _ = trial_and_levels(C, float(lam))
        rec.update(float_mu0=float(w[0]), float_mu1=float(w[1]))
        r_exact = C.rayleigh(lam, x)                                               # (e)
        r = F(-((-r_exact.numerator * 10 ** 9) // r_exact.denominator), 10 ** 9)   # rounded UP to 1e-9
        assert r >= r_exact
        rec.update(r=str(r), r_float=float(r))
        if not r < z < d: raise ArithmeticError('need r < z < d')
        neg, n, info = certified_inertia(C.K(lam, z, d), C.n)                       # (c),(d): Theorem 3
        rec.update(negative_eigenvalues_of_K=neg, inertia_info=info)
        if neg != 1: raise ArithmeticError('K(z) has %d negative eigenvalues, need exactly 1' % neg)
        # (f) controls
        zc = F(int(np.ceil((w[1] + 1e-3) * 10 ** 6)), 10 ** 6); rec['control_z'] = str(zc)
        if not zc < d: raise ArithmeticError('control point not below the floor')
        try:
            negc, _, _ = certified_inertia(C.K(lam, zc, d), C.n)
            rec['control_negative_eigenvalues'] = negc; control_rejected = negc != 1
        except ArithmeticError as ex:
            rec['control_negative_eigenvalues'] = 'uncertified: ' + str(ex); control_rejected = True
        if not control_rejected: raise ArithmeticError('control at z above E1 was ACCEPTED: construction wrong')
        gap = z - r; E0r, E1r, gr = REF[li]
        rec.update(gap_lower=str(gap), gap_float=float(gap), reference_gap=gr)
        if not float(gap) <= gr + 1e-9: raise ArithmeticError('bound exceeds the reference gap: construction wrong')
        if not (float(r) >= E0r - 1e-8 and float(z) <= E1r + 1e-8):
            raise ArithmeticError('r below reference E0 or z above reference E1: construction wrong')
        rec['status'] = 'CERTIFIED'
    except (ArithmeticError, AssertionError) as ex:
        rec['error'] = repr(ex)
    rec['seconds'] = time.time() - t0
    return rec


def propose(C, lam):
    """float proposal of (s, e, z) for one coupling; nothing here is trusted by the verifier."""
    E, sg, Sf, Mf = C.floats(); n = C.n; cp = float(C.cplus)
    A = np.diag(E + 6 * lam) - lam * Sf; w = sl.eigvalsh(A, subset_by_index=[0, 1]); best = None
    def zstar(s, e, its):
        d = s * cp + 2 * e
        f = lambda z: sl.eigvalsh(A - z * np.eye(n) - lam * lam * Mf / (d - z), subset_by_index=[1, 1])[0]
        lo, hi = w[0], min(w[1], d - 1e-6)
        if f(lo) <= 0: return None
        for _ in range(its):
            m = (lo + hi) / 2
            if f(m) > 0: lo = m
            else: hi = m
        return lo
    for s40 in range(26, 40):
        s = s40 / 40; e = np.floor((one_plaquette_float(lam, 3.5 * (1 - s)) - 2e-6) * 1e6) / 1e6
        zs = zstar(s, e, 12)
        if zs is not None and (best is None or zs > best[0]): best = (zs, s40, e)
    zs, s40, e = best; zs = zstar(s40 / 40, e, 30)
    z = np.floor((zs - 2e-5) * 1e5) / 1e5
    return dict(lam=str(int(lam)), ECUT=int(C.B.ECUT), s='%d/40' % s40, N=25, e='%d/1000000' % round(e * 1e6),
                z='%d/100000' % round(z * 1e5))


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--propose', action='store_true', help='re-derive the targets with floats and print them')
    ap.add_argument('--only', default='', help='comma list of couplings to run (default: all)')
    args = ap.parse_args(); t0 = time.time()
    targets = [T for T in TARGETS if not args.only or T['lam'] in args.only.split(',')]
    cells = {}
    def cell(ec):
        if ec not in cells:
            cells[ec] = Cell(F(ec)); C = cells[ec]
            print('exact build  ECUT = %s : retained n = %d, outside states reached = %d, boundary states = %d, '
                  'c_plus = %s, %.1f s' % (ec, C.n, C.nR, C.boundary, C.cplus, C.build_seconds), flush=True)
        return cells[ec]
    if args.propose:
        for T in targets:
            print('    ' + json.dumps(propose(cell(T['ECUT']), float(T['lam']))) + ',', flush=True)
        return 0
    nwords = check_against_repo19()
    print('cross-check with the repo exact Haar 19-state matrices: %d exact trace identities hold' % nwords, flush=True)
    nm = check_method()
    print('inertia method check: integer congruence + Gershgorin agrees with the repo exact rational LDL on %d '
          '19-state matrices (repo targets at lambda = 1 and 4 reproduced)' % nm, flush=True)
    rows = []; structure = {}
    for T in targets:
        C = cell(T['ECUT'])
        if T['ECUT'] not in structure:
            structure[T['ECUT']] = check_structure(C)
            print('  exact structure checks at ECUT = %s: %d commutation identities, %d character-rule entries, '
                  '%d norm-balance identities' % ((T['ECUT'],) + structure[T['ECUT']]), flush=True)
        rec = run_target(C, T); rows.append(rec)
        print('  lam = %s done in %.1f s: %s %s' % (T['lam'], rec['seconds'], rec['status'], rec.get('error', '')), flush=True)
    print()
    hdr = ('lam', 'ECUT', 'dim', 'd', 'r (>= E0)', 'z (<= E1)', 'certified gap >=', 'reference gap', 'old 19-state', 'status')
    print(' | '.join(hdr))
    for r in rows:
        li = int(r['lam'])
        print(' | '.join([r['lam'], r['ECUT'], str(r['n']), '%.6f' % r.get('d_float', float('nan')),
                          '%.9f' % r.get('r_float', float('nan')), '%.5f' % float(F(r['z'])),
                          '%.6f' % r['gap_float'] if 'gap_float' in r else 'n/a', '%.9f' % REF[li][2], OLD19[li],
                          r['status']]))
    print()
    for r in rows:
        if r['status'] == 'CERTIFIED':
            print('lam = %s: K(z) has exactly %d negative eigenvalue (n = %d, worst Gershgorin radius/centre %.2e); '
                  'control z = %s rejected (%s negative eigenvalues); gap >= %s'
                  % (r['lam'], r['negative_eigenvalues_of_K'], r['n'], r['inertia_info']['worst_radius_over_centre'],
                     r['control_z'], r['control_negative_eigenvalues'], r['gap_lower']))
    out = dict(model='two SU(3) squares sharing one link (theta graph, arms 1,3,3), alpha = 1',
               method='Schur inertia (Theorem 3) on the complete electric cutoff; exact rational matrices; '
                      'integer congruence + Gershgorin inertia count',
               cross_check_19_state_trace_identities=nwords, inertia_method_agreements=nm,
               structure_checks={str(k): v for k, v in structure.items()}, rows=rows, seconds=time.time() - t0,
               continuum_claim=False, lean=False)
    (HERE / 'certify_twosquare_extended.json').write_text(json.dumps(out, indent=1) + '\n')
    ok = bool(rows) and all(r['status'] == 'CERTIFIED' for r in rows)
    print('\ntotal %.1f s;  %s' % (time.time() - t0, 'ALL CERTIFIED' if ok else 'NOT ALL CERTIFIED'))
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
