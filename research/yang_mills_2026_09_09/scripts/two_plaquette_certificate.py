#!/usr/bin/env python3
"""Exact SU(3) shared-link two-plaquette Schur certificates.

Acceptance is Python-standard-library rational arithmetic. This is an actual
seven-link gauge graph, NOT two independent plaquettes. Written Hilbert-space
completeness and all-tail proofs are in proofs/TWO_PLAQUETTES.md.
Run: python -S two_plaquette_certificate.py --out output.json
Optional proposals/Monte Carlo cross-checks are separate programs.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from functools import lru_cache
from itertools import permutations, product, combinations
import json
from pathlib import Path
import time

Letter = tuple[str, int]
Word = tuple[Letter, ...]
TraceProduct = tuple[Word, ...]
U: Word = (("U", 1),)
Ub: Word = (("U", -1),)
V: Word = (("V", 1),)
Vb: Word = (("V", -1),)
R: Word = (("U", 1), ("V", -1))
Rb: Word = (("V", 1), ("U", -1))
# Constant, two orientations on each square, two on the outer rectangle.
BASIS: tuple[TraceProduct, ...] = ((), (U,), (Ub,), (V,), (Vb,), (R,), (Rb,))
BASIS_NAMES = ("1", "Tr U", "Tr U^dagger", "Tr V", "Tr V^dagger",
               "Tr(U V^dagger)", "Tr(V U^dagger)")
ELECTRIC = (F(0), F(16,3), F(16,3), F(16,3), F(16,3), F(8), F(8))
TAIL = F(28, 3)  # all omitted spin networks, not just chosen trace polynomials


def sign_perm(p: tuple[int, ...]) -> int:
    return -1 if sum(p[i] > p[j] for i in range(len(p)) for j in range(i+1, len(p))) % 2 else 1


def conjugate(t: TraceProduct) -> TraceProduct:
    return tuple(tuple((name, -sign) for name, sign in reversed(w)) for w in t)


def group_contractions(pos: list[tuple[int,int]], neg: list[tuple[int,int]]):
    """SU(3) Haar contractions for total degree <=4, exact in this domain.

    U(3) Weingarten k=1,2 when numbers balance; epsilon*epsilon/3! for
    three unpaired U's or conjugates. Outside declared domain: refuse.
    """
    p, q = len(pos), len(neg)
    if p + q > 4:
        raise ValueError("Haar kernel covers degree <=4 per independent SU(3) variable")
    if (p-q) % 3:
        return []
    if p == q == 0:
        return [(F(1), [])]
    if p == q == 1:
        return [(F(1,3), [(pos[0][0],neg[0][0]), (pos[0][1],neg[0][1])])]
    if p == q == 2:
        terms = []
        for a in permutations(range(2)):
            for b in permutations(range(2)):
                coefficient = F(1,8) if a == b else F(-1,24)
                pairs = [(pos[k][0],neg[a[k]][0]) for k in range(2)]
                pairs += [(pos[k][1],neg[b[k]][1]) for k in range(2)]
                terms.append((coefficient, pairs))
        return terms
    if (p,q) in ((3,0), (0,3)):
        triples = pos if p else neg
        return [(F(sign_perm(a),6), [(triples[k][0],triples[a[k]][1]) for k in range(3)])
                for a in permutations(range(3))]
    raise ValueError(f"Unsupported Haar bidegree {(p,q)}")


@lru_cache(maxsize=None)
def haar(t: TraceProduct) -> F:
    """Integral of a product of traces in independent Haar U,V in SU(3).

    Dummy indices run along trace cycles. Delta contractions are summed by
    union-find: every remaining index loop contributes a factor of three.
    """
    if any(not w for w in t):
        raise ValueError("Use the empty trace PRODUCT for 1; empty words are not admitted")
    groups = {"U": ([], []), "V": ([], [])}
    n = 0
    for w in t:
        ids = list(range(n,n+len(w))); n += len(w)
        for k, (name, sign) in enumerate(w):
            if name not in groups or sign not in (-1,1):
                raise ValueError("Invalid trace letter")
            i,j = ids[k],ids[(k+1)%len(w)]
            # (U^dagger)_{ij} = conjugate(U_{ji}).
            groups[name][0 if sign == 1 else 1].append((i,j) if sign == 1 else (j,i))
    left = group_contractions(*groups['U']); right = group_contractions(*groups['V'])
    result = F(0)
    for (ca,pa),(cb,pb) in product(left,right):
        parent = list(range(n))
        def root(i):
            while parent[i] != i:
                parent[i] = parent[parent[i]]; i = parent[i]
            return i
        for i,j in pa+pb:
            parent[root(i)] = root(j)
        components = len({root(i) for i in range(n)})
        result += ca*cb*3**components
    return result


def zero(n: int) -> list[list[F]]:
    return [[F(0) for _ in range(n)] for _ in range(n)]


def transpose(a):
    return [list(x) for x in zip(*a)]


def matmul(a,b):
    return [[sum((x*y for x,y in zip(row,col)),F(0)) for col in zip(*b)] for row in a]


def sub(a,b):
    return [[x-y for x,y in zip(ar,br)] for ar,br in zip(a,b)]


def inner(v,a,w):
    return sum((v[i]*a[i][j]*w[j] for i in range(len(v)) for j in range(len(w))),F(0))


def exact_inertia(a):
    """Exact rational LDL inertia. Reject zero pivots rather than infer signs."""
    if a != transpose(a):
        raise ValueError("Not a real symmetric matrix")
    m = [list(row) for row in a]; pivots=[]
    for k in range(len(m)):
        p=m[k][k]
        if not p:
            raise ArithmeticError(f"Zero LDL pivot at {k}; certificate not accepted")
        pivots.append(p)
        for i in range(k+1,len(m)):
            for j in range(i,len(m)):
                m[i][j] -= m[k][i]*m[k][j]/p
                m[j][i] = m[i][j]
    return sum(p<0 for p in pivots),pivots


@lru_cache(maxsize=1)
def matrices():
    n=len(BASIS); gram=zero(n); s=zero(n); s2=zero(n)
    four=(U,Ub,V,Vb)
    for i,j in product(range(n),repeat=2):
        outer=conjugate(BASIS[i])+BASIS[j]
        gram[i][j]=haar(outer)
        s[i][j]=sum((haar(outer+(w,)) for w in four),F(0))/2
        s2[i][j]=sum((haar(outer+(w,x)) for w,x in product(four,repeat=2)),F(0))/4
    m=sub(s2,matmul(s,s))
    expected=[[F(i==j) for j in range(n)] for i in range(n)]
    if gram != expected or s!=transpose(s) or m!=transpose(m):
        raise AssertionError("Haar/Gram/symmetry failure")
    return gram,s,s2,m


def retained(lam: F):
    _,s,_,m=matrices(); n=len(s)
    a=[[(ELECTRIC[i]+6*lam if i==j else F(0))-lam*s[i][j]
         for j in range(n)] for i in range(n)]
    return a,[[lam*lam*x for x in row] for row in m]


def schur(a,m,z,d=TAIL):
    if not z<d:
        raise ValueError("Test energy does not lie below the complete-tail lower bound")
    return [[a[i][j]-(z if i==j else 0)-m[i][j]/(d-z)
             for j in range(len(a))] for i in range(len(a))]


def qmatrix(a):
    return [[str(x) for x in row] for row in a]


def det_bareiss(a):
    """Independent exact determinant by permutation formula for small controls."""
    n=len(a)
    if not n:return F(1)
    return sum((F(sign_perm(p))*__import__('functools').reduce(
        lambda x,y:x*y,(a[i][p[i]] for i in range(n)),F(1))
        for p in permutations(range(n))),F(0))


def checks():
    count=0
    def require(b):
        nonlocal count
        if not b:raise AssertionError("Exact two-plaquette control failed")
        count+=1
    require(haar(())==1)
    for w in (U,Ub,V,Vb,R,Rb):
        require(haar((w,))==0)
        require(haar(conjugate((w,))+(w,))==1)
        require(haar((w,w,w))==1)
    require(haar((U,U,Ub,Ub))==2)
    require(haar((U+U,U))==-1)
    require(haar((U+U+U,))==1)
    require(haar((U+Ub,))==3)
    require(haar((U+Ub+U+Ub,))==3)
    require(haar((U,Ub,V,Vb))==1)
    gram,s,s2,m=matrices()
    require(gram==[[F(i==j) for j in range(7)] for i in range(7)])
    # Check PSD by all principal minors, including exact zeros. No rounding.
    for k in range(1,8):
        for ids in combinations(range(7),k):
            require(det_bareiss([[m[i][j] for j in ids] for i in ids])>=0)
    # Basis change reversing both orientations leaves real compression invariant.
    perm=(0,2,1,4,3,6,5)
    require(all(s[i][j]==s[perm[i]][perm[j]] for i,j in product(range(7),repeat=2)))
    # Swapping squares also exchanges the outer-loop orientations.
    perm=(0,3,4,1,2,6,5)
    require(all(m[i][j]==m[perm[i]][perm[j]] for i,j in product(range(7),repeat=2)))
    # Electric-tail lower bound from theta-graph arm lengths (1,3,3).
    # This finite test supports, not replaces, the all-irrep proof in the note.
    def c(p,q):return F(p*p+q*q+p*q+3*p+3*q,3)
    for p,q in product(range(15),repeat=2):
        if p+q:
            require(c(p,q)>=F(4,3))
            if p+q>=2:require(c(p,q)>=3)
    # Incorrect independent-plaquette electric assignment for the outer loop.
    require(3*F(4,3)+3*F(4,3)==8)
    require(4*F(4,3)+4*F(4,3)!=8)
    # Baryonic first-omitted theta state: f=Tr U Tr V, g=Tr(UV).
    # Gram [[1,1/3],[1/3,1]], shared-arm Casimir on (f,g)
    # [[7/3,1],[1,7/3]], so f-g has shared Casimir 4/3.
    f=(U,V); g=(U+V,)
    require(haar(conjugate(f)+f)==1)
    require(haar(conjugate(g)+g)==1)
    require(haar(conjugate(f)+g)==F(1,3))
    require(haar(conjugate(f)+f)+haar(conjugate(g)+g)
            -2*haar(conjugate(f)+g)==F(4,3))
    require(F(7,3)-1+6*F(4,3)==TAIL)
    # A zero-containing pivot and a degree-overflow input MUST be refused.
    rejected=0
    for fn in (lambda: exact_inertia([[F(0),F(1)],[F(1),F(0)]]),
               lambda: haar((U,U,U,U,U,Ub)),
               lambda: schur(*retained(F(1)),TAIL)):
        try:fn()
        except (ArithmeticError,ValueError):rejected+=1
    require(rejected==3)
    return count,rejected


def certify(lam: F, r: F, z: F, d: F=TAIL):
    a,m=retained(lam); n=len(a)
    if not 0<=lam or not r<z<d:
        raise ValueError("lambda>=0 and r<z<d required; d must have a separate complete-tail proof")
    ar=[[a[i][j]-(r if i==j else 0) for j in range(n)] for i in range(n)]
    az=[[a[i][j]-(z if i==j else 0) for j in range(n)] for i in range(n)]
    nr,pr=exact_inertia(ar); nz,pz=exact_inertia(az); nk,pk=exact_inertia(schur(a,m,z,d))
    if nr!=1 or nz!=1 or nk!=1:
        raise ArithmeticError(f"Wrong inertia: {(nr,nz,nk)}")
    return dict(lambda_over_alpha=str(lam),alpha='1',retained_dimension=7,
                complete_electric_cutoff='8',complete_hidden_floor=str(d),
                E0_upper=str(r),E1_lower=str(z),gap_lower=str(z-r),
                gap_display=float(z-r),negative_pivots=[nr,nz,nk],
                pivot_witnesses=[[str(x) for x in piv] for piv in (pr,pz,pk)],
                full_infinite_representation_tail=True,shared_link=True,
                lean_certificate=False,continuum_claim=False)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out',type=Path,default=Path('two_plaquette_results.json'))
    ap.add_argument('--targets',type=Path,default=Path(__file__).with_name('two_plaquette_targets.json'))
    args=ap.parse_args();t=time.monotonic(); nchecks,nrejected=checks()
    targets=json.loads(args.targets.read_text())
    results=[certify(F(t['lambda']),F(t['r']),F(t['z'])) for t in targets]
    payload=dict(model='two elementary SU(3) squares sharing one link; seven links; alpha=1',
                 basis=list(BASIS_NAMES),electric_energies=list(map(str,ELECTRIC)),
                 exact_checks=nchecks,deliberately_rejected_controls=nrejected,
                 rational_matrices=dict(zip(('Gram','S','S2','BBstar_over_lambda2'),
                                              (qmatrix(a) for a in matrices()))),
                 certificates=results,elapsed_seconds=time.monotonic()-t)
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(payload,indent=2)+'\n')
    print(json.dumps({k:v for k,v in payload.items() if k not in ('rational_matrices','certificates')},indent=2))
    for r in results:print('lambda/alpha',r['lambda_over_alpha'],'gap >=',r['gap_lower'])
    print('Output:',args.out)

if __name__=='__main__':main()
