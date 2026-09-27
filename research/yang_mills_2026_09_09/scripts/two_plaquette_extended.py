#!/usr/bin/env python3
"""Complete SU(3) theta-graph electric cutoff C<=12 (15 states), exact Haar.

This extends the seven-state checker without treating nonorthonormal vectors as
orthonormal. All quadratic matrices retain the exact positive diagonal Gram.
The bidegrees used by this cutoff require total degree at most six per SU(3)
variable. General higher degrees are refused. See the written basis proof.
"""
from __future__ import annotations
from fractions import Fraction as F
from itertools import product,permutations,combinations
from functools import lru_cache
import argparse,json,time
from pathlib import Path
import two_plaquette_certificate as tp
import su3_character_certificate as su

U,Ub,V,Vb,R,Rb=tp.U,tp.Ub,tp.V,tp.Vb,tp.R,tp.Rb
Poly=tuple[tuple[F,tp.TraceProduct],...]

def mon(t):return ((F(1),t),)
def pc(p):return tuple((c,tp.conjugate(t)) for c,t in p)
# Ordering groups exact electric eigenspaces. No square roots in the basis.
bary=((F(1),(U,V)),(F(-1),(U+V,)))
octet=((F(1),(U,Vb)),(F(-1,3),(R,)))
sextet=((F(1),(U,V)),(F(1),(U+V,)))
BASIS=tuple(mon(t) for t in tp.BASIS)+(bary,pc(bary),octet,pc(octet),
       sextet,pc(sextet),((F(1),(U,Ub)),(F(-1),())),
       ((F(1),(V,Vb)),(F(-1),())))
ENERGY=tp.ELECTRIC+(F(28,3),F(28,3),F(11),F(11),F(34,3),F(34,3),F(12),F(12))
NAMES=tp.BASIS_NAMES+('TrU TrV-Tr(UV)','conjugate baryon',
       'TrU TrVdag-Tr(UVdag)/3','conjugate shared adjoint',
       'TrU TrV+Tr(UV)','conjugate shared sextet','abs(TrU)^2-1','abs(TrV)^2-1')
GRAM_DIAG=tuple(map(F,[1]*7))+(F(4,3),F(4,3),F(8,9),F(8,9),F(8,3),F(8,3),F(1),F(1))
TAIL=F(40,3)


def inv(a):
    n=len(a);m=[list(row)+[F(i==j) for j in range(n)] for i,row in enumerate(a)]
    for k in range(n):
        pivot=next((i for i in range(k,n) if m[i][k]),None)
        if pivot is None:raise ArithmeticError('Singular exact matrix')
        m[k],m[pivot]=m[pivot],m[k];v=m[k][k];m[k]=[x/v for x in m[k]]
        for i in range(n):
            if i!=k:
                v=m[i][k];m[i]=[x-v*y for x,y in zip(m[i],m[k])]
    return [r[n:] for r in m]


def epsilon(x):
    return tp.sign_perm(tuple(x)) if len(set(x))==3 else 0


def gram_invariants(p,q,structures):
    # structures are (delta index pairs, ordered epsilon triples).
    n=len(structures);g=[[0]*n for _ in range(n)]
    for values in product(range(3),repeat=p+q):
        vv=[]
        for pairs,eps in structures:
            v=int(all(values[i]==values[j] for i,j in pairs))
            for triple in eps:v*=epsilon([values[i] for i in triple])
            vv.append(v)
        for i in range(n):
            if vv[i]:
                for j in range(n):g[i][j]+=vv[i]*vv[j]
    return [[F(x) for x in row] for row in g]


@lru_cache(maxsize=None)
def invariant_basis(p,q):
    if (p,q)==(4,1):
        st=[([(k,4)], [tuple(j for j in range(4) if j!=k)]) for k in range(3)]
    elif (p,q)==(6,0):
        allst=[]
        for pair in combinations(range(1,6),2):
            a=(0,)+pair;b=tuple(i for i in range(6) if i not in a)
            allst.append(([],[a,b]))
        g=gram_invariants(p,q,allst);ids=[]
        for i in range(len(allst)):
            new=ids+[i]
            try:inv([[g[k][j] for j in new] for k in new])
            except ArithmeticError:continue
            ids=new
        if len(ids)!=5:raise AssertionError('Wrong degree-six invariant rank')
        st=[allst[i] for i in ids]
    else:raise ValueError('Unsupported unbalanced bidegree')
    g=gram_invariants(p,q,st)
    return st,inv(g)


def contractions(pos,neg):
    p,q=len(pos),len(neg)
    if p+q>6:raise ValueError('Extended Haar domain is total degree <=6 per SU(3) variable')
    if (p-q)%3:return []
    if p+q<=4:return tp.group_contractions(pos,neg)
    if (p,q)==(3,3):
        terms=[]
        for a,b in product(permutations(range(3)),repeat=2):
            relative=tuple(a.index(b[k]) for k in range(3))
            fixed=sum(i==relative[i] for i in range(3))
            c=F(7,120) if fixed==3 else F(-1,40) if fixed==1 else F(1,60)
            pairs=[(pos[k][0],neg[a[k]][0]) for k in range(3)]
            pairs += [(pos[k][1],neg[b[k]][1]) for k in range(3)]
            terms.append((c,pairs))
        return terms
    if p<q:return contractions(neg,pos)
    st,gi=invariant_basis(p,q);entries=pos+neg;out={}
    for i,(pairsA,epsA) in enumerate(st):
        for j,(pairsB,epsB) in enumerate(st):
            c=gi[i][j]
            if not c:continue
            fixed=[(entries[a][0],entries[b][0]) for a,b in pairsA]
            fixed += [(entries[a][1],entries[b][1]) for a,b in pairsB]
            for ps in product(tuple(permutations(range(3))),repeat=len(epsA)):
                cc=c;pairs=fixed.copy()
                for ea,eb,perm in zip(epsA,epsB,ps):
                    cc*=tp.sign_perm(perm)
                    pairs += [(entries[ea[k]][0],entries[eb[perm[k]]][1]) for k in range(3)]
                key=tuple(sorted(tuple(sorted(v)) for v in pairs))
                out[key]=out.get(key,F(0))+cc
    return [(c,list(k)) for k,c in out.items() if c]


@lru_cache(maxsize=None)
def haar(t):
    if any(not w for w in t):raise ValueError('No empty trace words')
    groups={'U':([],[]),'V':([],[])};n=0
    for w in t:
        ids=list(range(n,n+len(w)));n+=len(w)
        for k,(name,sgn) in enumerate(w):
            if name not in groups or sgn not in (-1,1):raise ValueError('Invalid trace letter')
            i,j=ids[k],ids[(k+1)%len(w)]
            groups[name][0 if sgn==1 else 1].append((i,j) if sgn==1 else (j,i))
    ans=F(0)
    for (c,pa),(d,pb) in product(contractions(*groups['U']),contractions(*groups['V'])):
        parent=list(range(n))
        def root(i):
            while parent[i]!=i:parent[i]=parent[parent[i]];i=parent[i]
            return i
        for i,j in pa+pb:parent[root(i)]=root(j)
        ans+=c*d*3**len({root(i) for i in range(n)})
    return ans


def expectation(a,b,extra=()):
    return sum((ca*cb*haar(tp.conjugate(ta)+tb+extra)
                for ca,ta in a for cb,tb in b),F(0))


@lru_cache(maxsize=1)
def matrices():
    n=len(BASIS);g=tp.zero(n);s=tp.zero(n);s2=tp.zero(n);four=(U,Ub,V,Vb)
    for i in range(n):
        for j in range(i,n):
            a,b=BASIS[i],BASIS[j]
            g[i][j]=g[j][i]=expectation(a,b)
            s[i][j]=s[j][i]=sum((expectation(a,b,(w,)) for w in four),F(0))/2
            s2[i][j]=s2[j][i]=sum((expectation(a,b,(w,v)) for w,v in product(four,repeat=2)),F(0))/4
    if g!=[[GRAM_DIAG[i] if i==j else F(0) for j in range(n)] for i in range(n)]:
        raise AssertionError('Exact polynomial basis Gram differs from spin-network norms')
    m=[[s2[i][j]-sum((s[i][k]*s[k][j]/GRAM_DIAG[k] for k in range(n)),F(0))
        for j in range(n)] for i in range(n)]
    return g,s,s2,m


def psd_check(a):
    m=[r.copy() for r in a];piv=[]
    for k in range(len(m)):
        d=m[k][k];piv.append(d)
        if d<0:raise ArithmeticError('Negative PSD pivot')
        if d==0:
            if any(m[k][j] for j in range(k+1,len(m))):raise ArithmeticError('Zero pivot with nonzero row')
            continue
        for i in range(k+1,len(m)):
            for j in range(i,len(m)):
                m[i][j]-=m[k][i]*m[k][j]/d;m[j][i]=m[i][j]
    return piv


def retained(lam):
    g,s,s2,m=matrices();n=len(g)
    a=[[(ENERGY[i]+6*lam)*g[i][j]-lam*s[i][j] for j in range(n)] for i in range(n)]
    return g,a,[[lam*lam*x for x in row] for row in m]


def certify(lam,r,z,d):
    if lam<0 or not r<z<d:raise ValueError('Invalid coupling or energy order')
    g,a,m=retained(lam);n=len(g)
    ar=[[a[i][j]-r*g[i][j] for j in range(n)] for i in range(n)]
    az=[[a[i][j]-z*g[i][j] for j in range(n)] for i in range(n)]
    km=[[az[i][j]-m[i][j]/(d-z) for j in range(n)] for i in range(n)]
    records=[tp.exact_inertia(x) for x in (ar,az,km)]
    if [x[0] for x in records]!=[1,1,1]:raise ArithmeticError('Outer inertia failed')
    return dict(lambda_over_alpha=str(lam),E0_upper=str(r),E1_lower=str(z),
                hidden_floor=str(d),gap_lower=str(z-r),gap_display=float(z-r),
                negative_pivots=[a for a,b in records],
                pivot_witnesses=[[str(x) for x in b] for a,b in records])


def certify_row(t):
    lam,r,z,s=map(F,(t['lambda'],t['r'],t['z'],t['s']))
    n=t['N'];kap=F(7,2)*(1-s)
    if not 0<s<1 or kap!=F(t['kappa']) or not isinstance(n,int) or n<1:
        raise ValueError('Invalid allocation')
    e=F(t['single_floor'])
    if e>=kap*su.tail_floor(n):raise ValueError('Inner energy above its tail')
    neg,ps=su.interval_inertia(n,lam/kap,e/kap,schur=True)
    if neg or any(lo<=0 for lo,hi in ps):raise ArithmeticError('Local floor not proved')
    d=s*TAIL+2*e
    if F(t['d'])!=d:raise ValueError('Wrong derived tail')
    row=certify(lam,r,z,d)
    row.update(s=str(s),kappa=str(kap),single_floor=str(e),inner_N=n,
               inner_negative_pivots=neg,inner_scale=str(su.SCALE),inner_pivots=ps)
    return row


def checks():
    count=0
    def req(b):
        nonlocal count
        if not b:raise AssertionError('Extended exact check failed')
        count+=1
    req(len(BASIS)==15)
    # Independent lower-order implementation, all words up to four letters.
    letters=(('U',1),('U',-1),('V',1),('V',-1))
    for n in range(1,5):
        for w in product(letters,repeat=n):req(haar((w,))==tp.haar((w,)))
    req(haar((U,U,U,Ub,Ub,Ub))==6)
    req(haar((U,U,U,U,Ub))==3)
    req(haar((U,U,U,U,U,U))==5)
    req(haar((U+Ub+U+Ub+U+Ub,))==3)
    g,s,s2,m=matrices();req(all(x>0 for x in GRAM_DIAG))
    psd_check(m);req(True)
    # Matrix construction used upper triangle; check selected reversed entries.
    four=(U,Ub,V,Vb)
    for i in range(15):
        for j in range(i):
            req(expectation(BASIS[i],BASIS[j])==g[i][j])
            req(sum((expectation(BASIS[i],BASIS[j],(w,)) for w in four),F(0))/2==s[i][j])
    # Complete leading block matches the independent 7-state Haar implementation.
    old=tp.matrices()
    for k in range(3):req([row[:7] for row in (g,s,s2)[k][:7]]==old[k])
    # M changes with the larger projection; copying old M would be wrong.
    req([row[:7] for row in m[:7]]!=old[3])
    refused=0
    for fn in (lambda:haar((U,)*7),lambda:psd_check([[F(0),F(1)],[F(1),F(0)]])):
        try:fn()
        except (ValueError,ArithmeticError):refused+=1
    req(refused==2)
    return count,refused


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--targets',type=Path,default=Path(__file__).with_name('two_plaquette_extended_targets.json'))
    ap.add_argument('--out',type=Path,default=Path('two_plaquette_extended_results.json'))
    ap.add_argument('--checks-only',action='store_true')
    args=ap.parse_args();start=time.monotonic();n,r=checks()
    rows=[] if args.checks_only else [certify_row(t) for t in json.loads(args.targets.read_text())]
    payload=dict(model='Two SU(3) squares sharing one link; alpha=1',
                 cutoff='12',dimension=15,omitted_electric_floor=str(TAIL),
                 basis=NAMES,electric=list(map(str,ENERGY)),Gram_diagonal=list(map(str,GRAM_DIAG)),
                 checks=n,refused_controls=r,
                 matrices=dict(zip(('Gram','S','S2','coupling_Gram'),map(tp.qmatrix,matrices()))),
                 certificates=rows,total_inertia_certificates=4*len(rows),
                 total_pivot_signs=sum(45+len(row['inner_pivots']) for row in rows),
                 elapsed_seconds=time.monotonic()-start,continuum_claim=False,
                 formal_Haar_or_operator_proof=False)
    args.out.parent.mkdir(parents=True,exist_ok=True);args.out.write_text(json.dumps(payload,indent=2)+'\n')
    print('Exact checks',n,'refusals',r,'seconds',payload['elapsed_seconds'])
    for row in rows:print(row['lambda_over_alpha'],'gap >=',row['gap_lower'],'=',row['gap_display'])
    print('Output',args.out)

if __name__=='__main__':main()
