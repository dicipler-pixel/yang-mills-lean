# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Jeromie Beasley. See LICENSING.md at the repository root.
"""Exact SU(3) Kogut-Susskind Hamiltonian on the periodic ring (ladder) of L plaquettes,
in a spin-network basis with exact rational vertex intertwiners (Green, ring_flux_cert).

Graph: vertices B_i (bottom), T_i (top), i in Z_L.  Links: b_i: B_i->B_{i+1}, t_i: T_i->T_{i+1},
v_i: B_i->T_i.  Plaquette i: B_i -b_i-> B_{i+1} -v_{i+1}-> T_{i+1} -t_i^{-1}-> T_i -v_i^{-1}-> B_i.
H = sum_links C2 + lam * sum_p (3 - Re tr U_p)   (units g^2/2; repo convention).
Sector = cut triality n_cut = tri(b_i) + tri(t_i) mod 3 (same for every i by Gauss's law).
"""
from fractions import Fraction as F
from functools import lru_cache
from collections import Counter
from itertools import product
import su3rep as S

# ---------------- graph ----------------
def ring_graph(L):
    links = {}
    for i in range(L):
        links[('b', i)] = (('B', i), ('B', (i+1) % L))
        links[('t', i)] = (('T', i), ('T', (i+1) % L))
        links[('v', i)] = (('B', i), ('T', i))
    order = []
    for i in range(L):
        order += [('v', i), ('b', i), ('t', i)]
    verts = {}
    for i in range(L):
        verts[('B', i)] = [(('b', i), 'out'), (('b', (i-1) % L), 'in'), (('v', i), 'out')]
        verts[('T', i)] = [(('t', i), 'out'), (('t', (i-1) % L), 'in'), (('v', i), 'in')]
    plaqs = []
    for i in range(L):
        plaqs.append([(('b', i), +1), (('v', (i+1) % L), +1), (('t', i), -1), (('v', i), -1)])
    return dict(L=L, links=links, order=order, verts=verts, plaqs=plaqs,
                horizontal=[l for l in order if l[0] in 'bt'])

def square_graph():
    """Single plaquette (4 links) for validation: gauge-invariant states = class functions, E = 4 C2."""
    links = {('a', 0): ('x0', 'x1'), ('a', 1): ('x1', 'x2'), ('a', 2): ('x3', 'x2'), ('a', 3): ('x0', 'x3')}
    verts = {'x0': [(('a', 0), 'out'), (('a', 3), 'out')], 'x1': [(('a', 0), 'in'), (('a', 1), 'out')],
             'x2': [(('a', 1), 'in'), (('a', 2), 'in')], 'x3': [(('a', 2), 'out'), (('a', 3), 'in')]}
    plaqs = [[(('a', 0), 1), (('a', 1), 1), (('a', 2), -1), (('a', 3), -1)]]
    return dict(L=1, links=links, order=list(links), verts=verts, plaqs=plaqs, horizontal=[])

# ---------------- fast multiplicities (for enumeration only) ----------------
@lru_cache(maxsize=None)
def weights(p, q):
    """GL3 weight multiset of (p,q) via Gelfand-Tsetlin patterns, normalised mod (1,1,1)."""
    m13, m23, m33 = p+q, q, 0
    c = Counter()
    for m12 in range(m23, m13+1):
        for m22 in range(m33, m23+1):
            for m11 in range(m22, m12+1):
                s1 = m11; s2 = m12+m22; s3 = m13+m23+m33
                w = (s1, s2-s1, s3-s2)
                c[(w[0]-w[2], w[1]-w[2])] += 1
    return c

def dual_pq(pq, role):
    return pq if role == 'in' else (pq[1], pq[0])

@lru_cache(maxsize=None)
def inv_dim(legs):
    """Multiplicity of the trivial rep in the tensor product of the legs (out legs dualised)."""
    reps = [dual_pq(pq, r) for pq, r in legs]
    if sum(S.triality(*r) for r in reps) % 3: return 0
    c = Counter({(0, 0): 1})
    for r in reps[:-1]:
        n = Counter()
        for w1, m1 in c.items():
            for w2, m2 in weights(*r).items():
                n[(w1[0]+w2[0], w1[1]+w2[1])] += m1*m2
        c = n
    last = (reps[-1][1], reps[-1][0])   # need dual of last inside product of the others
    mult = 0
    c = Counter(c)
    while c:
        hw = max((w for w, m in c.items() if m), key=lambda w: (2*w[0]+w[1], w[0]))
        pq = (hw[0]-hw[1], hw[1])
        k = c[hw]
        if pq == last: mult = k
        for w, m in weights(*pq).items():
            c[w] -= k*m
        c = Counter({w: m for w, m in c.items() if m})
    return mult

def reps_upto(cmax):
    out = []
    for p in range(0, 12):
        for q in range(0, 12):
            if S.casimir(p, q) <= cmax: out.append((p, q))
    return sorted(out, key=lambda r: (S.casimir(*r), r))

def enumerate_configs(G, emax, sector=None, emin=None):
    """All link-irrep configurations with total Casimir <= emax (and > emin if given), every vertex
    invariant space nonzero, cut triality == sector (if given).  Returns list of (E, config dict)."""
    order = G['order']; reps = reps_upto(emax)
    vert_links = {v: [l for l, _ in legs] for v, legs in G['verts'].items()}
    done_at = {}
    for v, ls in vert_links.items():
        k = max(order.index(l) for l in ls); done_at.setdefault(k, []).append(v)
    out = []
    cfg = {}
    def rec(k, e):
        if k == len(order):
            if emin is not None and e <= emin: return
            if sector is not None and G['L'] and (S.triality(*cfg[('b', 0)]) + S.triality(*cfg[('t', 0)])) % 3 != sector: return
            out.append((e, dict(cfg))); return
        for r in reps:
            c2 = S.casimir(*r)
            if e + c2 > emax: break
            cfg[order[k]] = r
            ok = True
            for v in done_at.get(k, []):
                legs = tuple((cfg[l], role) for l, role in G['verts'][v])
                if inv_dim(legs) == 0: ok = False; break
            if ok: rec(k+1, e + c2)
            del cfg[order[k]]
    rec(0, F(0))
    return out

def theta_graph():
    """Two squares sharing one link (repo two-square cell, arms 1,3,3) for validation."""
    links = {('s', 0): ('a', 'b'), ('c', 1): ('b', 'c'), ('c', 2): ('c', 'd'), ('c', 3): ('d', 'a'),
             ('e', 1): ('b', 'e'), ('e', 2): ('e', 'f'), ('e', 3): ('f', 'a')}
    verts = {}
    for l, (s, t) in links.items():
        verts.setdefault(s, []).append((l, 'out')); verts.setdefault(t, []).append((l, 'in'))
    plaqs = [[(('s', 0), 1), (('c', 1), 1), (('c', 2), 1), (('c', 3), 1)],
             [(('s', 0), 1), (('e', 1), 1), (('e', 2), 1), (('e', 3), 1)]]
    return dict(L=0, links=links, order=list(links), verts=verts, plaqs=plaqs, horizontal=[])
