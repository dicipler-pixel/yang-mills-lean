#!/usr/bin/env python3
"""SU(3) single-loop spectral certificates; Python 3 standard-library verifier.

Run: python su3_character_certificate.py
Re-propose targets with NumPy/SciPy: python su3_character_certificate.py --generate
All acceptance decisions use exact integer outward interval arithmetic, never
floating-point eigenvalue output. This is not a Lean formalization.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse, hashlib, json, math, random, time

ROOT=Path(__file__).resolve().parent
BITS=192
SCALE=1 << BITS
ZERO=(0,0)


def ceildiv(a,b):
    return -((-a)//b)


def enclose(x):
    x=F(x)
    return (x.numerator*SCALE//x.denominator,
            ceildiv(x.numerator*SCALE,x.denominator))


def sub(a,b):
    return (a[0]-b[1],a[1]-b[0])


def product_quotient(a,b,c):
    """Enclose (a/S)*(b/S)/(c/S) on the fixed integer grid /S."""
    if c[0] <= 0 <= c[1]:
        raise ArithmeticError('pivot interval contains zero')
    pp=(a[0]*b[0],a[0]*b[1],a[1]*b[0],a[1]*b[1])
    pl,ph=min(pp),max(pp)
    ends=[(x,y) for x in (pl,ph) for y in c]
    # Python // is mathematical floor even for negative denominators.
    return (min(x//y for x,y in ends),max(ceildiv(x,y) for x,y in ends))


def states(n):
    return [(p,s-p) for s in range(n+1) for p in range(s+1)]


def neighbors(p,q):
    return [(a,b) for a,b in ((p+1,q),(p-1,q+1),(p,q-1),
             (p,q+1),(p+1,q-1),(p-1,q)) if min(a,b)>=0]


def casimir(p,q):
    return F(p*p+q*q+p*q+3*p+3*q,3)


def tail_floor(n):
    s=n+1
    return F(s*s-(s*s//4)+3*s,3)


def matrix_entries(n,lam,shift=F(0),schur=False):
    ss=states(n); index={s:i for i,s in enumerate(ss)}
    entries={}
    for i,(p,q) in enumerate(ss):
        entries[i,i]=casimir(p,q)+3*lam-shift
        for t in neighbors(p,q):
            j=index.get(t)
            if j is not None and i<j:
                entries[i,j]=-lam/2
    if schur:
        d=tail_floor(n)
        assert shift < d
        correction=lam*lam/(4*(d-shift))
        start=n*(n+1)//2
        for i in range(start,len(ss)):
            entries[i,i]-=2*correction
            if i+1<len(ss):
                entries[i,i+1]=entries.get((i,i+1),F(0))-correction
    return len(ss),entries


def interval_inertia(n,lam,shift,schur=False):
    """Exact outward interval symmetric elimination; signs certify inertia.

    Every exact Schur entry is enclosed inductively. Since no enclosed pivot
    crosses zero, the exact unpivoted LDL decomposition exists and Sylvester's
    inertia law makes its negative-pivot count exact. Banded symmetric Gaussian
    elimination introduces no entries outside the initial half-bandwidth.
    """
    size,entries=matrix_entries(n,lam,shift,schur)
    bw=max(j-i for i,j in entries)
    mat=[[ZERO for _ in range(min(bw+1,size-i))] for i in range(size)]
    for (i,j),value in entries.items():
        mat[i][j-i]=enclose(value)
    pivots=[]
    count=0
    for k in range(size):
        pivot=mat[k][0]
        if pivot[0]<=0<=pivot[1]:
            raise ArithmeticError(f'uncertified pivot {k}: {pivot}')
        count+=int(pivot[1]<0)
        pivots.append(pivot)
        end=min(size,k+bw+1)
        for i in range(k+1,end):
            a=mat[k][i-k]
            if a==ZERO:
                continue
            for j in range(i,end):
                b=mat[k][j-k]
                if b!=ZERO:
                    mat[i][j-i]=sub(mat[i][j-i],product_quotient(a,b,pivot))
    return count,pivots


def determinant3(a):
    return (a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])
           -a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])
           +a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0]))


def character(p,q,z):
    # Weyl alternant for partition (p+q,q,0); z0*z1*z2=1.
    exponents=(p+q+2,q+1,0)
    return determinant3([[v**k for k in exponents] for v in z])/determinant3(
        [[v**k for k in (2,1,0)] for v in z])


def structural_checks():
    checks=0
    rng=random.Random(260908)
    for _ in range(1000):
        a=F(rng.randint(-1000,1000),rng.randint(1,999))
        b=F(rng.randint(-1000,1000),rng.randint(1,999))
        c=F(rng.choice((-1,1))*rng.randint(1,1000),rng.randint(1,999))
        interval=product_quotient(enclose(a),enclose(b),enclose(c))
        exact=a*b/c
        assert F(interval[0],SCALE)<=exact<=F(interval[1],SCALE)
        checks+=1
    # Independent character evaluation checks the rule, including chamber walls.
    for z in ((F(2),F(3),F(1,6)),(F(3,2),F(5,3),F(2,5)),
              (F(-2),F(-3),F(1,6))):
        for p,q in states(25):
            chi=character(p,q,z)
            fundamental=sum(character(a,b,z) for a,b in
                 ((p+1,q),(p-1,q+1),(p,q-1)) if min(a,b)>=0)
            antifund=sum(character(a,b,z) for a,b in
                 ((p,q+1),(p+1,q-1),(p-1,q)) if min(a,b)>=0)
            assert sum(z)*chi==fundamental
            assert sum(1/v for v in z)*chi==antifund
            checks+=2
    for n in range(31):
        ss=states(n); index=set(ss)
        # Verify actual boundary adjacency against the stated rectangular B.
        edges=[((p,q),t) for p,q in ss for t in neighbors(p,q) if t not in index]
        expected=[((p,n-p),t) for p in range(n+1) for t in
                   ((p+1,n-p),(p,n-p+1))]
        assert sorted(edges)==sorted(expected)
        assert tail_floor(n)==min(casimir(p,n+1-p) for p in range(n+2))
        for s in range(n+1,n+20):
            assert all(casimir(p,s-p)>=tail_floor(n) for p in range(s+1))
        # Integer BB* (before factor lambda^2/4): diagonal2, nearest neighbors1.
        for p in range(n+1):
            for r in range(n+1):
                outgoing_p={(p+1,n-p),(p,n-p+1)}
                outgoing_r={(r+1,n-r),(r,n-r+1)}
                assert len(outgoing_p & outgoing_r)==(2 if p==r else 1 if abs(p-r)==1 else 0)
                checks+=1
        checks+=2
    # Small-case inertia independently checked against Fraction elimination.
    for n,lam,shift,schur in ((2,F(1),F(13,5),False),(3,F(1),F(15,4),True),
                              (2,F(1,10),F(37,100),False)):
        size,entries=matrix_entries(n,lam,shift,schur)
        mat=[[F(0) for _ in range(size)] for _ in range(size)]
        for (i,j),value in entries.items():mat[i][j]=mat[j][i]=value
        exact_negative=0
        for k in range(size):
            assert mat[k][k]!=0
            exact_negative+=int(mat[k][k]<0)
            for i in range(k+1,size):
                for j in range(i,size):
                    mat[i][j]-=mat[k][i]*mat[k][j]/mat[k][k]
                    mat[j][i]=mat[i][j]
        got,_=interval_inertia(n,lam,shift,schur)
        assert exact_negative==got
        checks+=1
    return checks


def sqrt_upper(x,digits=16):
    """Exact rational upper bound for nonnegative sqrt(x)."""
    x=F(x); scale=10**digits
    floor=math.isqrt((x.numerator*scale*scale)//x.denominator)
    result=F(floor+1,scale)
    assert result*result>=x
    return result


def generate_targets():
    import numpy as np
    from scipy.sparse import coo_matrix,eye
    from scipy.sparse.linalg import eigsh
    def scipy_mat(n,lam,shift=F(0),schur=False):
        size,entries=matrix_entries(n,lam,shift,schur)
        rr=[];cc=[];vv=[]
        for (i,j),x in entries.items():
            rr.append(i);cc.append(j);vv.append(float(x))
            if i!=j:rr.append(j);cc.append(i);vv.append(float(x))
        return coo_matrix((vv,(rr,cc)),shape=(size,size)).tocsr()
    target=[]
    for ls,n in [('1/10',3),('1',6),('10',10),('100',25)]:
        lam=F(ls); a=scipy_mat(n,lam)
        v0=np.linspace(1,2,a.shape[0])
        eig=np.sort(eigsh(a,k=3,which='SA',return_eigenvectors=False,tol=1e-12,v0=v0))
        box=[]
        for ev in eig[:2]:
            box.append([str(F(math.floor(ev*10**7)-2,10**7)),
                        str(F(math.ceil(ev*10**7)+2,10**7))])
        left=(eig[0]+eig[1])/2;right=min(eig[1],float(tail_floor(n))-1e-3)
        for _ in range(36):
            mid=(left+right)/2
            sm=scipy_mat(n,lam,F(str(mid)),True)
            se=np.sort(eigsh(sm,k=2,which='SA',return_eigenvectors=False,tol=1e-12,v0=v0))
            if se[1]>0:left=mid
            else:right=mid
        z=F(math.floor(left*10**7)-5,10**7)
        target.append(dict(lambda_over_kappa=ls,N=n,finite_eigenvalue_enclosures=box,
                           schur_z=str(z),numerical_finite_eigenvalues=eig.tolist()))
    (ROOT/'certificate_targets.json').write_text(json.dumps(target,indent=2)+'\n')


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--generate',action='store_true')
    args=ap.parse_args()
    if args.generate:generate_targets()
    started=time.time(); checks=structural_checks()
    print('Exact structural/arithmetic assertions:',checks,flush=True)
    targets=json.loads((ROOT/'certificate_targets.json').read_text())
    results=[];witnesses=[]
    for target in targets:
        lam=F(target['lambda_over_kappa']);n=target['N'];records=[]
        boxes=[[F(s) for s in box] for box in target['finite_eigenvalue_enclosures']]
        for i,(lo,hi) in enumerate(boxes):
            for endpoint,expect,label in ((lo,i,'lower'),(hi,i+1,'upper')):
                count,pivots=interval_inertia(n,lam,endpoint)
                assert count==expect,(lam,n,i,label,count,expect)
                records.append(dict(kind='finite',level=i,endpoint=label,shift=str(endpoint),
                                    negative_pivots=count,pivots=pivots))
        z=F(target['schur_z']);count,pivots=interval_inertia(n,lam,z,True)
        assert count==1 and z>boxes[0][1] and z<tail_floor(n)
        records.append(dict(kind='boundary_schur',shift=str(z),negative_pivots=count,pivots=pivots))
        d=tail_floor(n);lo1=boxes[1][0];hi0=boxes[0][1]
        scalar=(lo1+d-sqrt_upper((d-lo1)**2+4*lam**2))/2-hi0
        gap=z-hi0
        row=dict(lambda_over_kappa=str(lam),kappa='1',N=n,dimension=(n+1)*(n+2)//2,
            omitted_casimir_min=str(d),boundary_norm_upper=str(lam),
            finite_eigenvalue_enclosures=[[str(v) for v in box] for box in boxes],
            numerical_finite_eigenvalues=target['numerical_finite_eigenvalues'],
            scalar_gap_lower_exact=str(scalar),scalar_gap_lower_display=float(scalar),
            schur_E1_lower=str(z),E0_upper=str(hi0),
            full_single_loop_gap_lower_exact=str(gap),full_single_loop_gap_lower_display=float(gap),
            certified=True,verification='exact outward integer interval LDL inertia; 192-bit grid',
            lean_formalized=False,continuum_yang_mills_claim=False)
        results.append(row)
        witnesses.append(dict(lambda_over_kappa=str(lam),N=n,scale=str(SCALE),records=records))
        print(json.dumps({k:row[k] for k in ('lambda_over_kappa','N','dimension',
             'scalar_gap_lower_display','full_single_loop_gap_lower_display')}),flush=True)
    analytic=dict(lambda_over_kappa='0',kappa='1',N=1,dimension=3,E0='0',E1='4/3',
        full_single_loop_gap_lower_exact='4/3',full_single_loop_gap_lower_display=4/3,
        certified=True,verification='exact diagonal Casimir spectrum',
        lean_formalized=False,continuum_yang_mills_claim=False)
    payload=dict(model='H=kappa*C2+lambda*(3-Re chi_(1,0)) on L2(SU3)^Ad',
        assumptions='kappa>0, lambda>=0; dimensionless normalization kappa=1',
        arithmetic_assertions=checks,interval_inertia_certificates=sum(len(w['records']) for w in witnesses),
        total_pivots_checked=sum(len(r['pivots']) for w in witnesses for r in w['records']),
        results=[analytic]+results,elapsed_seconds=time.time()-started)
    (ROOT/'su3_results.json').write_text(json.dumps(payload,indent=2)+'\n')
    (ROOT/'interval_pivot_witnesses.json').write_text(json.dumps(witnesses,separators=(',',':'))+'\n')
    print('Completed',payload['interval_inertia_certificates'],'exact inertia certificates;',
          payload['total_pivots_checked'],'pivot signs;',round(payload['elapsed_seconds'],3),'seconds',flush=True)

if __name__=='__main__':main()
