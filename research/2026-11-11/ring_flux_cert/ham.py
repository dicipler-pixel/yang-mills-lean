# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Jeromie Beasley. See LICENSING.md at the repository root.
"""Exact assembly of H = E + lam*B on a truncated spin-network basis (Green, ring_flux_cert).

P  = every link-irrep configuration of the sector with electric energy E <= cap (all intertwiners).
Q1 = configurations with E > cap reached from P by one plaquette operator.
Returns exact sparse rational data:
  gram[c]           vertex-Gram Kronecker block of configuration c (times prod 1/d_link)
  Bcol[j]           coordinates of B b_j = sum_p (3 - Re tr U_p) b_j over P u Q1, for every j in P
All coordinates refer to the (non-orthonormal, rational) product intertwiner basis.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
import su3rep as S
import ring as R

@lru_cache(maxsize=None)
def inv_basis(legs):
    """Basis of invariants for legs, plus pivot keys and inverse for exact coordinates."""
    B = S.vertex_invariants(legs)
    n = len(B)
    if n == 0: return None
    keys = sorted({k for b in B for k in b})
    rows = [[b.get(k, F(0)) for b in B] for k in keys]
    # choose n independent rows greedily
    red, piv = [], []
    sel = []
    basis_rows = []
    for ri, row in enumerate(rows):
        cand = basis_rows + [row]
        r, p = S.rref(cand, n)
        if len(r) > len(basis_rows):
            basis_rows.append(row); sel.append(keys[ri])
            if len(sel) == n: break
    sub = [[r[i] for i in range(n)] for r in basis_rows]
    inv = S.matinv(sub)
    gram = [[S.tensor_inner(x, y, legs) for y in B] for x in B]
    return dict(B=B, n=n, sel=sel, inv=inv, gram=gram)

def coords_in(legs, T):
    ib = inv_basis(legs)
    y = [T.get(k, F(0)) for k in ib['sel']]
    c = [sum((ib['inv'][i][j]*y[j] for j in range(ib['n']) if y[j]), F(0)) for i in range(ib['n'])]
    # exactness check: T == sum c_i B_i
    recon = {}
    for ci, b in zip(c, ib['B']):
        if ci:
            for k, v in b.items(): recon[k] = recon.get(k, F(0)) + ci*v
    recon = {k: v for k, v in recon.items() if v}
    Tn = {k: v for k, v in T.items() if v}
    if recon != Tn: raise ArithmeticError('corner tensor not in intertwiner span')
    return c

@lru_cache(maxsize=None)
def amaps(pq, f):
    return S.append_maps(S.irrep(*pq), f)

@lru_cache(maxsize=None)
def corner_map(old_legs, x, fx, newx, y, fy, newy):
    """Local exact map Inv(old_legs) -> Inv(new_legs) at a plaquette corner.
    Legs x and y are the two plaquette links at this corner; leg role 'out' (link source) uses E,
    'in' (link target) uses F; their new fundamental indices are contracted (delta)."""
    new_legs = list(old_legs)
    new_legs[x] = (newx, old_legs[x][1]); new_legs[y] = (newy, old_legs[y][1])
    new_legs = tuple(new_legs)
    nb = inv_basis(new_legs); ob = inv_basis(old_legs)
    if nb is None or ob is None: return None
    def M(pos, f, new):
        pq, role = old_legs[pos]
        E, Fm = amaps(pq, f)[new]
        d = S.irrep(*pq).d; dn = S.irrep(*new).d
        out = {}
        for i in range(d):
            for a in range(3):
                for k in range(dn):
                    v = E[3*i+a][k] if role == 'out' else Fm[k][3*i+a]
                    if v: out.setdefault((i, a), []).append((k, v))
        return out
    Mx = M(x, fx, newx); My = M(y, fy, newy)
    cols = []
    for I in ob['B']:
        T = {}
        for key, v in I.items():
            for a in range(3):
                for kx, vx in Mx.get((key[x], a), ()):
                    for ky, vy in My.get((key[y], a), ()):
                        nk = list(key); nk[x] = kx; nk[y] = ky; nk = tuple(nk)
                        T[nk] = T.get(nk, F(0)) + v*vx*vy
        cols.append(coords_in(new_legs, T))
    return [[cols[j][i] for j in range(ob['n'])] for i in range(nb['n'])]

class Model:
    def __init__(self, G):
        self.G = G
        self.vorder = sorted(G['verts'])
        self.lpos = {l: k for k, l in enumerate(G['order'])}
    def legs(self, cfg, v):
        return tuple((cfg[self.lpos[l]], role) for l, role in self.G['verts'][v])
    def energy(self, cfg):
        return sum((S.casimir(*r) for r in cfg), F(0))
    def hor(self, cfg):
        return sum((S.casimir(*cfg[self.lpos[l]]) for l in self.G['horizontal']), F(0))
    def vdims(self, cfg):
        out = []
        for v in self.vorder:
            ib = inv_basis(self.legs(cfg, v))
            out.append(0 if ib is None else ib['n'])
        return out
    def gram_block(self, cfg):
        """Kronecker product of vertex Grams times prod 1/d_link, as dict {(mi,mj): F}."""
        g = {((), ()): F(1)}
        for v in self.vorder:
            gv = inv_basis(self.legs(cfg, v))['gram']
            g2 = {}
            for (a, b), val in g.items():
                for i in range(len(gv)):
                    for j in range(len(gv)):
                        if gv[i][j]: g2[(a+(i,), b+(j,))] = val*gv[i][j]
            g = g2
        s = F(1)
        for r in cfg: s /= S.irrep(*r).d
        return {k: v*s for k, v in g.items()}
    def plaquette_images(self, cfg, p, conj=False):
        """Yield (new_cfg, {vertex_index: matrix}) terms of tr U_p (or tr U_p^dag) acting on cfg."""
        G = self.G; path = G['plaqs'][p]
        steps = []
        for link, dr in path:
            f = '3' if (dr > 0) != conj else '3b'
            steps.append((link, f))
        # corners: vertex at start of step k
        corners = []
        for k, (link, dr) in enumerate(path):
            s, t = G['links'][link]
            corners.append(s if dr > 0 else t)
        options = []
        for link, f in steps:
            options.append(list(amaps(cfg[self.lpos[link]], f).keys()))
        for choice in product(*options):
            new = list(cfg)
            for (link, f), nr in zip(steps, choice): new[self.lpos[link]] = nr
            new = tuple(new)
            mats = {}
            ok = True
            for k, v in enumerate(corners):
                prev = (k-1) % 4
                legs = self.legs(cfg, v)
                names = [l for l, _ in G['verts'][v]]
                x = names.index(steps[prev][0]); y = names.index(steps[k][0])
                m = corner_map(legs, x, steps[prev][1], choice[prev], y, steps[k][1], choice[k])
                if m is None: ok = False; break
                mats[self.vorder.index(v)] = m
            if ok: yield new, mats

def kron_apply(mats, dims_old, dims_new, idx):
    """Image of product basis vector idx (tuple) under the Kronecker product (identity off-corner)."""
    res = {(): F(1)}
    for vi, i in enumerate(idx):
        m = mats.get(vi)
        r2 = {}
        if m is None:
            for k, v in res.items(): r2[k+(i,)] = v
        else:
            for k, v in res.items():
                for a in range(dims_new[vi]):
                    if m[a][i]: r2[k+(a,)] = v*m[a][i]
        res = r2
    return res

def build(G, sector, cap):
    mod = Model(G)
    Pcfg = [tuple(c[l] for l in G['order']) for e, c in R.enumerate_configs(G, F(cap), sector)]
    Pset = set(Pcfg)
    states = []; index = {}
    def add_cfg(c):
        dims = mod.vdims(c)
        for idx in product(*[range(d) for d in dims]):
            index[(c, idx)] = len(states); states.append((c, idx))
    for c in Pcfg: add_cfg(c)
    nP = len(states)
    Bcol = []
    qcfgs = set()
    for j in range(nP):
        c, idx = states[j]
        dims_old = mod.vdims(c)
        col = {}
        col[(c, idx)] = F(3*len(G['plaqs']))
        for p in range(len(G['plaqs'])):
            for conj in (False, True):
                for new, mats in mod.plaquette_images(c, p, conj):
                    dims_new = mod.vdims(new)
                    for nidx, v in kron_apply(mats, dims_old, dims_new, idx).items():
                        key = (new, nidx)
                        col[key] = col.get(key, F(0)) - v/2
                    if new not in Pset: qcfgs.add(new)
        Bcol.append({k: v for k, v in col.items() if v})
    for c in sorted(qcfgs): add_cfg(c)
    gram = {}
    for c in list(Pcfg) + sorted(qcfgs): gram[c] = mod.gram_block(c)
    return dict(model=mod, states=states, index=index, nP=nP, Bcol=Bcol, gram=gram,
                Pcfg=Pcfg, Qcfg=sorted(qcfgs), cap=F(cap), sector=sector)
