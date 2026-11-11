# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Jeromie Beasley. See LICENSING.md at the repository root.
"""Exact rational SU(3) representation data for spin networks (Green, ring_flux_cert).

Irrep (p,q) is realised as the symmetric traceless subspace of V^{(x)p} (x) V*^{(x)q}
(V* carries U-bar). Every basis vector is a rational weight vector of the ambient tensor
space, whose standard inner product is U(3)-invariant, so the Gram matrix M_R is rational.
Everything here is exact (fractions.Fraction); no floats.
"""
from fractions import Fraction as F
from itertools import product, combinations_with_replacement
from functools import lru_cache
from collections import Counter

def casimir(p, q):
    return F(p*p + q*q + p*q + 3*p + 3*q, 3)

def dim(p, q):
    return (p+1)*(q+1)*(p+q+2)//2

def triality(p, q):
    return (p - q) % 3

# ---------------- exact linear algebra on lists of Fractions ----------------
def rref(rows, ncols):
    """Row-reduce a list of rows (lists of F); returns (reduced rows, pivot cols)."""
    m = [list(r) for r in rows]
    piv = []; r = 0
    for c in range(ncols):
        k = next((i for i in range(r, len(m)) if m[i][c] != 0), None)
        if k is None: continue
        m[r], m[k] = m[k], m[r]
        inv = 1 / m[r][c]
        m[r] = [x*inv for x in m[r]]
        for i in range(len(m)):
            if i != r and m[i][c] != 0:
                f = m[i][c]; mr = m[r]
                m[i] = [a - f*b for a, b in zip(m[i], mr)]
        piv.append(c); r += 1
        if r == len(m): break
    return m[:r], piv

def nullspace(rows, ncols):
    red, piv = rref(rows, ncols)
    free = [c for c in range(ncols) if c not in set(piv)]
    basis = []
    for f in free:
        v = [F(0)]*ncols; v[f] = F(1)
        for r, pc in zip(red, piv):
            v[pc] = -r[f]
        basis.append(v)
    return basis

def solve_in_span(B, y):
    """B: list of column vectors (lists), y vector; exact coefficients c with sum c_k B_k = y."""
    n = len(B); m = len(y)
    rows = [[B[k][i] for k in range(n)] + [y[i]] for i in range(m) if any(B[k][i] for k in range(n)) or y[i]]
    red, piv = rref(rows, n+1)
    if n in piv: raise ArithmeticError('vector not in span')
    c = [F(0)]*n
    for r, pc in zip(red, piv): c[pc] = r[n]
    return c

def matinv(a):
    n = len(a)
    m = [list(row) + [F(int(i == j)) for j in range(n)] for i, row in enumerate(a)]
    red, piv = rref(m, 2*n)
    if piv[:n] != list(range(n)): raise ArithmeticError('singular')
    return [r[n:] for r in red]

def matmul(a, b):
    bt = list(zip(*b))
    return [[sum((x*y for x, y in zip(r, c) if x and y), F(0)) for c in bt] for r in a]

# ---------------- ambient tensors ----------------
# ambient index: tuple of length p+q, entries 0..2; first p slots are V, last q are V*.

def irrep_basis(p, q):
    """Weight basis of symmetric traceless tensors. Returns list of (weight, ambient dict)."""
    out = []
    Vms = list(combinations_with_replacement(range(3), p))
    Wms = list(combinations_with_replacement(range(3), q))
    byw = {}
    for A in Vms:
        for B in Wms:
            ca, cb = Counter(A), Counter(B)
            w = tuple(ca[k] - cb[k] for k in range(3))
            byw.setdefault(w, []).append((A, B))
    for w in sorted(byw):
        cells = byw[w]; idx = {c: i for i, c in enumerate(cells)}
        eqs = []
        if p > 0 and q > 0:
            cons = {}
            for (A, B) in cells:
                ca, cb = Counter(A), Counter(B)
                for k in range(3):
                    if ca[k] and cb[k]:
                        A1 = list(A); A1.remove(k); B1 = list(B); B1.remove(k)
                        cons.setdefault((tuple(A1), tuple(B1)), []).append(idx[(A, B)])
            for key, lst in cons.items():
                row = [F(0)]*len(cells)
                for i in lst: row[i] += 1
                eqs.append(row)
        ns = nullspace(eqs, len(cells)) if eqs else [[F(int(i == j)) for i in range(len(cells))] for j in range(len(cells))]
        for v in ns:
            amb = {}
            for (A, B), c in zip(cells, v):
                if c == 0: continue
                for oa in set(perms(A)):
                    for ob in set(perms(B)):
                        amb[oa + ob] = amb.get(oa + ob, F(0)) + c
            out.append((w, amb))
    assert len(out) == dim(p, q), (p, q, len(out))
    return out

def perms(t):
    from itertools import permutations
    return permutations(t)

def dot(x, y):
    if len(x) > len(y): x, y = y, x
    return sum((v*y[k] for k, v in x.items() if k in y), F(0))

def act(Y, p, q, x):
    """Lie algebra element Y = E_ab (a,b) acting on ambient dict x (V: E_ab, V*: -E_ba)."""
    a, b = Y
    out = {}
    for idx, v in x.items():
        for s in range(p+q):
            if s < p:
                if idx[s] == b:
                    n = idx[:s] + (a,) + idx[s+1:]; out[n] = out.get(n, F(0)) + v
            else:
                if idx[s] == a:
                    n = idx[:s] + (b,) + idx[s+1:]; out[n] = out.get(n, F(0)) - v
    return {k: v for k, v in out.items() if v}

GENS = [(0, 1), (1, 0), (1, 2), (2, 1)]  # raising E01,E12 and lowering; with weights these generate sl3

class Irrep:
    def __init__(self, p, q):
        self.p, self.q = p, q
        self.d = dim(p, q); self.c2 = casimir(p, q); self.tri = triality(p, q)
        bas = irrep_basis(p, q)
        self.weights = [w for w, _ in bas]
        self.amb = [a for _, a in bas]
        self.M = [[dot(x, y) for y in self.amb] for x in self.amb]
        self.Minv = matinv(self.M)
        self.keys = sorted({k for a in self.amb for k in a})
    def coords(self, y):
        """Orthogonal projection coordinates (M^{-1} B^T y) of an ambient dict y."""
        bty = [dot(x, y) for x in self.amb]
        return [sum((self.Minv[i][j]*bty[j] for j in range(self.d) if bty[j]), F(0)) for i in range(self.d)]
    @property
    def rho(self):
        if not hasattr(self, '_rho'):
            self._rho = {}
            for Y in GENS:
                cols = [self.coords(act(Y, self.p, self.q, b)) for b in self.amb]
                self._rho[Y] = [[cols[j][i] for j in range(self.d)] for i in range(self.d)]
        return self._rho

@lru_cache(maxsize=None)
def irrep(p, q):
    return Irrep(p, q)

EPS = {(0,1,2):1,(1,2,0):1,(2,0,1):1,(0,2,1):-1,(2,1,0):-1,(1,0,2):-1}

def append_maps(R, f):
    """Equivariant decomposition of R (x) f, f in {'3','3b'}.
    Returns dict target(p',q') -> (E, F): F is d' x 3d (row-major lists), E is 3d x d',
    product coordinates ordered (i, a) -> 3*i + a, with F E = 1 and sum E F = 1."""
    p, q = R.p, R.q
    if f == '3':
        targets = [((p+1, q), 'id'), ((p, q-1), 'contr'), ((p-1, q+1), 'eps')]
    else:
        targets = [((p, q+1), 'id'), ((p-1, q), 'contr'), ((p+1, q-1), 'eps')]
    res = {}
    for (pp, qq), kind in targets:
        if pp < 0 or qq < 0: continue
        T = irrep(pp, qq)
        cols = []
        for i in range(R.d):
            for a in range(3):
                y = {}
                for idx, v in R.amb[i].items():
                    Vp, Wq = idx[:p], idx[p:]
                    if f == '3':
                        if kind == 'id':
                            k = Vp + (a,) + Wq; y[k] = y.get(k, F(0)) + v
                        elif kind == 'contr':
                            if Wq[0] == a:
                                k = Vp + Wq[1:]; y[k] = y.get(k, F(0)) + v
                        else:
                            for m in range(3):
                                e = EPS.get((a, Vp[0], m))
                                if e:
                                    k = Vp[1:] + (m,) + Wq; y[k] = y.get(k, F(0)) + e*v
                    else:
                        if kind == 'id':
                            k = Vp + Wq + (a,); y[k] = y.get(k, F(0)) + v
                        elif kind == 'contr':
                            if Vp[0] == a:
                                k = Vp[1:] + Wq; y[k] = y.get(k, F(0)) + v
                        else:
                            for m in range(3):
                                e = EPS.get((a, Wq[0], m))
                                if e:
                                    k = Vp + (m,) + Wq[1:]; y[k] = y.get(k, F(0)) + e*v
                y = {k: v for k, v in y.items() if v}
                cols.append(T.coords(y))
        Fm = [[cols[c][r] for c in range(3*R.d)] for r in range(T.d)]
        assert any(any(row) for row in Fm), ('zero map', R.p, R.q, f, pp, qq)
        # adjoint F^dag = (M_R (x) I)^{-1} F^T M_T
        FtM = matmul([list(r) for r in zip(*Fm)], T.M)  # 3d x d'
        Edag = []
        for i in range(R.d):
            for a in range(3):
                Edag.append([sum((R.Minv[i][j]*FtM[3*j+a][k] for j in range(R.d) if R.Minv[i][j]), F(0)) for k in range(T.d)])
        FE = matmul(Fm, Edag)
        c = FE[0][0]
        assert all(FE[i][j] == (c if i == j else 0) for i in range(T.d) for j in range(T.d)), 'Schur scalar fails'
        E = [[x/c for x in row] for row in Edag]
        res[(pp, qq)] = (E, Fm)
    # completeness: sum E F = 1
    n = 3*R.d
    S = [[F(0)]*n for _ in range(n)]
    for E, Fm in res.values():
        EF = matmul(E, Fm)
        for i in range(n):
            for j in range(n): S[i][j] += EF[i][j]
    assert all(S[i][j] == (1 if i == j else 0) for i in range(n) for j in range(n)), 'completeness fails'
    return res

# ---------------- vertex invariants ----------------
def leg_rho(R, role, Y):
    m = R.rho[Y]
    if role == 'in':
        return m
    return [[-m[j][i] for j in range(R.d)] for i in range(R.d)]

def leg_weight(R, role, i):
    w = R.weights[i]
    return w if role == 'in' else tuple(-x for x in w)

@lru_cache(maxsize=None)
def vertex_invariants(legs):
    """legs: tuple of ((p,q), role). Returns list of invariant tensors as dicts {(i1,..,in): F}."""
    Rs = [irrep(*pq) for pq, _ in legs]; roles = [r for _, r in legs]
    n = len(legs)
    tri = sum((R.tri if r == 'in' else -R.tri) for R, r in zip(Rs, roles)) % 3
    if tri: return []
    zero = []
    for idx in product(*[range(R.d) for R in Rs]):
        w = [0, 0, 0]
        for R, r, i in zip(Rs, roles, idx):
            lw = leg_weight(R, r, i)
            for k in range(3): w[k] += lw[k]
        if w[0] == w[1] == w[2]: zero.append(idx)  # SU(3) weight zero (GL3 weight mod (1,1,1))
    if not zero: return []
    col = {t: c for c, t in enumerate(zero)}
    eqs = {}
    for Y in [(0, 1), (1, 2)]:
        mats = [leg_rho(R, r, Y) for R, r in zip(Rs, roles)]
        for t, c in col.items():
            for s in range(n):
                m = mats[s]; i = t[s]
                for k in range(Rs[s].d):
                    v = m[k][i]
                    if v:
                        key = (Y,) + t[:s] + (k,) + t[s+1:]
                        eqs.setdefault(key, {})
                        eqs[key][c] = eqs[key].get(c, F(0)) + v
    rows = []
    for e in eqs.values():
        row = [F(0)]*len(zero)
        for c, v in e.items(): row[c] = v
        if any(row): rows.append(row)
    ns = nullspace(rows, len(zero)) if rows else [[F(int(i == j)) for i in range(len(zero))] for j in range(len(zero))]
    return [{zero[c]: v for c, v in enumerate(vec) if v} for vec in ns]

def leg_metric(R, role):
    return R.M if role == 'in' else R.Minv

def tensor_inner(x, y, legs):
    """Invariant inner product of two vertex tensors (real rational)."""
    Ms = [leg_metric(irrep(*pq), r) for pq, r in legs]
    tot = F(0)
    for kx, vx in x.items():
        for ky, vy in y.items():
            prod_ = vx*vy
            for M, a, b in zip(Ms, kx, ky):
                m = M[a][b]
                if not m: prod_ = 0; break
                prod_ *= m
            if prod_: tot += prod_
    return tot
