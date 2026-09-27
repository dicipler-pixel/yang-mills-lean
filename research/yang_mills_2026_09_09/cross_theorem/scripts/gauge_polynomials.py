#!/usr/bin/env python3
"""Exact trace polynomials, SU(3) electric action, and product Haar integration.

All edges are explicit independent original links. Tree gauge fixing is used only
for Haar integration; the electric action is performed BEFORE tree contraction.
The Fierz identity uses Tr(T_a T_b)=delta_ab/2. No floating arithmetic here.
"""
from __future__ import annotations
from fractions import Fraction as F
from functools import lru_cache
from itertools import product,combinations
import two_plaquette_certificate as old

@lru_cache(None)
def word(w):
    a=[]
    for x in w:
        if a and a[-1]==(x[0],-x[1]):a.pop()
        else:a.append(x)
    while len(a)>1 and a[0]==(a[-1][0],-a[-1][1]):a=a[1:-1]
    if not a:return ()
    return min(tuple(a[i:]+a[:i])for i in range(len(a)))

def mon(words):
    coefficient=F(1);out=[]
    for w in words:
        w=word(tuple(w))
        if w:out.append(w)
        else:coefficient*=3
    return {tuple(sorted(out)):coefficient}

def add(*polys):
    out={}
    for p in polys:
        for m,c in p.items():out[m]=out.get(m,F(0))+c
    return {m:c for m,c in out.items()if c}

def scale(p,c):return {m:c*v for m,v in p.items()if c*v}
def mul(p,q):
    out={}
    for a,ca in p.items():
        for b,cb in q.items():
            m=tuple(sorted(a+b));out[m]=out.get(m,F(0))+ca*cb
    return {m:c for m,c in out.items()if c}

def conjugate(p):
    out={}
    for m,c in p.items():
        pp=mon([tuple((e,-sgn)for e,sgn in reversed(w))for w in m])
        out=add(out,scale(pp,c))
    return out

@lru_cache(None)
def electric_mon(m):
    """-sum_e,a d_e,a^2 from every original link occurrence and exact Fierz.

    A negative letter places its left-derivative generator AFTER that letter;
    a positive one places it BEFORE. Same-trace pairs split that trace; different
    traces join. This distinguishes a repeated link from an independent one.
    """
    terms=[{m:F(4,3)*sum(map(len,m))}]
    occ={}
    for k,w in enumerate(m):
        for i,(edge,sgn)in enumerate(w):occ.setdefault(edge,[]).append((k,i,sgn))
    for occurrences in occ.values():
        for (k,i,sgn),(l,j,tgn)in combinations(occurrences,2):
            c=F(sgn*tgn);terms.append({m:-c/3})
            if k!=l:
                a,b=m[k],m[l];ia=(i+(sgn<0))%len(a);jb=(j+(tgn<0))%len(b)
                A=a[ia:]+a[:ia];B=b[jb:]+b[:jb]
                new=[w for h,w in enumerate(m)if h not in(k,l)]+[A+B]
            else:
                a=m[k];ia=(i+(sgn<0))%len(a);jb=(j+(tgn<0))%len(a);ia,jb=sorted((ia,jb))
                new=[w for h,w in enumerate(m)if h!=k]+[a[ia:jb],a[jb:]+a[:ia]]
            terms.append(scale(mon(new),c))
    return tuple(sorted(add(*terms).items()))

def electric(p):return add(*(scale(dict(electric_mon(m)),c)for m,c in p.items()))
def qkey(p):return tuple(sorted(p.items()))

@lru_cache(None)
def haar_mon(m):
    groups={};n=0
    for w in m:
        ids=list(range(n,n+len(w)));n+=len(w)
        for k,(edge,sgn)in enumerate(w):
            i,j=ids[k],ids[(k+1)%len(w)];pos,neg=groups.setdefault(edge,([],[]))
            (pos if sgn==1 else neg).append((i,j)if sgn==1 else(j,i))
    choices=[old.group_contractions(*v)for v in groups.values()]
    if any(not x for x in choices):return F(0)
    ans=F(0)
    for factors in product(*choices):
        parent=list(range(n));c=F(1)
        def root(i):
            while parent[i]!=i:parent[i]=parent[parent[i]];i=parent[i]
            return i
        for coeff,pairs in factors:
            c*=coeff
            for i,j in pairs:parent[root(i)]=root(j)
        ans+=c*3**len({root(i)for i in range(n)})
    return ans

def tree_reduce(p,chords):
    return add(*(scale(mon([tuple(x for x in w if x[0]in chords)for w in m]),c)for m,c in p.items()))

def integrate(p,chords):
    return sum((c*haar_mon(m)for m,c in tree_reduce(p,chords).items()),F(0))

def inner(p,q,chords):return integrate(mul(conjugate(p),q),chords)

def polynomial_equal_function(p,q,chords):return inner(add(p,scale(q,-1)),add(p,scale(q,-1)),chords)==0

def casimir_candidates(a,b):
    """Energy support of a product of two simple fundamental Wilson traces.

    One occurrence on an edge is 3 or bar3 (C=4/3); two equal occurrences are
    6+bar3 or conjugate (C=10/3 or4/3); two opposite are1+8 (C=0 or3).
    Returns an overcomplete spectral support, not a Gauss-law multiplicity count.
    """
    edges={}
    for w in(a,b):
        if len({e for e,s in w})!=len(w):raise ValueError('Spectral support requires each input loop simple in links')
        for e,s in w:edges.setdefault(e,[]).append(s)
    energies={F(0)}
    for signs in edges.values():
        values=[F(4,3)]if len(signs)==1 else([F(4,3),F(10,3)]if signs[0]==signs[1]else[F(0),F(3)])
        energies={x+y for x in energies for y in values}
    return sorted(energies)

def spectral_parts(a,b):
    f=mon([w for w in (a,b)if w]);energies=casimir_candidates(a,b);parts={}
    for e in energies:
        v=f
        for t in energies:
            if t!=e:v=scale(add(electric(v),scale(v,-t)),1/(e-t))
        parts[e]=v
    return parts

def serialize(p):return [{'traces':[[list(x)for x in w]for w in m],'coefficient':str(c)}for m,c in sorted(p.items())]
