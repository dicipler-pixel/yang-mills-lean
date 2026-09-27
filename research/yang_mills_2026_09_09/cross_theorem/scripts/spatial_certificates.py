#!/usr/bin/env python3
"""Exact full-tail certificates for explicit finite spatial SU(3) gauge graphs.

Default acceptance uses only standard-library rational/interval arithmetic.
--propose uses NumPy/SciPy for candidate endpoints, NEVER for acceptance.
The energy-resolved correction retains all finite Casimir components of B*P;
the omitted D itself remains infinite-dimensional. See the operator proof.
"""
from __future__ import annotations
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
import argparse,json,time,math
import spatial_gauge as sg
import two_plaquette_certificate as tp
import two_plaquette_extended as ext
import su3_character_certificate as su

ROOT=Path(__file__).resolve().parent

def allocation_coeffs(m):
    counts={e:sum(e in [x for x,s in w]for w in m['face_words'])for e in range(len(m['edges']))}
    if any(v==0 for v in counts.values()):raise ValueError('Unallocated links in this simple split')
    return [sum((F(1,counts[e])for e,s in w),F(0))for w in m['face_words']]

def retained(m,d,lam):
    n=len(m['energies']);A=[[((m['energies'][i]+3*len(m['faces'])*lam)if i==j else F(0))-lam*d['S'][i][j]for j in range(n)]for i in range(n)]
    return A

def positive_matrix(a):
    return ext.psd_check(a)

def correction(m,d,lam,s,offset,z,mode):
    floor=s*m['tail']+offset
    if not floor>z:raise ValueError('Test point reaches full omitted-sector floor')
    n=len(m['energies'])
    if mode=='resolved':
        return [[lam*lam*sum((a[i][j]/(s*e+offset-z)for e,a in d['masses'].items()),F(0))for j in range(n)]for i in range(n)]
    if mode=='scalar_floor':return [[lam*lam*x/(floor-z)for x in row]for row in d['M']]
    raise ValueError('Unknown correction mode')

def interval_inertia(a):
    """Dense outward integer-interval LDL on the inherited 192-bit grid."""
    if a!=tp.transpose(a):raise ValueError('Nonsymmetric matrix')
    m=[[su.enclose(x)for x in row]for row in a];pivots=[]
    for k in range(len(m)):
        p=m[k][k]
        if p[0]<=0<=p[1]:raise ArithmeticError('Uncertified dense interval pivot')
        pivots.append(p)
        for i in range(k+1,len(m)):
            if m[k][i]==su.ZERO:continue
            for j in range(i,len(m)):
                if m[k][j]!=su.ZERO:
                    m[i][j]=su.sub(m[i][j],su.product_quotient(m[k][i],m[k][j],p));m[j][i]=m[i][j]
    return sum(hi<0 for lo,hi in pivots),pivots

@lru_cache(None)
def mass_positivity(name):
    m,d=sg.calculate(name)
    return {str(e):list(map(str,positive_matrix(a)))for e,a in d['masses'].items()}

def validate_target(t):
    name=t['model'];m,d=sg.calculate(name);lam=F(t['lambda']);alpha=F(t.get('alpha','1'))
    if alpha!=1 or lam<0:raise ValueError('This stored normalization requires alpha=1,lambda>=0')
    s=F(t['s']);r=F(t['r']);z=F(t['z']);mode=t['mode']
    if not 0<s<=1:raise ValueError('Require0<s<=1')
    inners=[];offset=F(0);coefs=allocation_coeffs(m)
    if s==1:
        if t['local_floors']:raise ValueError('Unallocated electric case has no local floor')
    else:
        if len(t['local_floors'])!=len(coefs):raise ValueError('One local floor per plaquette required')
        for coef,tt in zip(coefs,t['local_floors']):
            kappa=(1-s)*coef;e=F(tt['e']);N=tt['N']
            if isinstance(N,bool)or not isinstance(N,int)or N<1 or kappa!=F(tt['kappa'])or e>=kappa*su.tail_floor(N):raise ValueError('Invalid local floor normalization')
            neg,piv=su.interval_inertia(N,lam/kappa,e/kappa,schur=True)
            if neg or any(lo<=0 for lo,hi in piv):raise ArithmeticError('Local ground lower bound fails')
            offset+=e;inners.append(dict(kappa=str(kappa),e=str(e),N=N,scale=str(su.SCALE),pivots=piv))
    floor=s*m['tail']+offset
    if F(t['d'])!=floor or not r<z<floor:raise ValueError('Wrong derived full-tail floor or endpoint order')
    A=retained(m,d,lam);n=len(A);corr=correction(m,d,lam,s,offset,z,mode)
    ar=[[A[i][j]-(r if i==j else 0)for j in range(n)]for i in range(n)]
    az=[[A[i][j]-(z if i==j else 0)for j in range(n)]for i in range(n)]
    K=tp.sub(az,corr);outer=[interval_inertia(x)for x in(ar,az,K)]
    if any(neg!=1 for neg,ps in outer):raise ArithmeticError('One negative direction and n-1 positive directions not established')
    mass_positivity(name)
    if any(1/(floor-z)-1/(s*e+offset-z)<0 for e in d['masses']):raise AssertionError('Resolved bound not dominated by scalar floor')
    return dict(model=name,links=len(m['edges']),plaquettes=len(m['faces']),dimension=n,
                mode=mode,lambda_over_alpha=str(lam),alpha='1',r=str(r),z=str(z),d=str(floor),s=str(s),offset=str(offset),
                gap_lower=str(z-r),gap_display=float(z-r),local_floor_certificates=inners,
                outer_negative_counts=[q[0]for q in outer],outer_pivot_scale=str(su.SCALE),outer_pivots=[q[1]for q in outer],
                energy_shells=list(map(str,d['masses'])),full_tail_proof='SPATIAL_BASES.md; LOCAL_ENERGY_FLOORS.md; RESOLVED_BOUNDARY.md',
                continuum_claim=False,uniform_volume_claim=False,accepted=True)

@lru_cache(None)
def local_proposal(lam,kappa,N=12):
    import numpy as np
    from scipy.linalg import eigh
    if kappa<=0:raise ValueError('Positive local kappa required')
    n,en=su.matrix_entries(N,lam/kappa);a=np.zeros((n,n))
    for(i,j),x in en.items():a[i,j]=a[j,i]=float(x)
    tail=float(su.tail_floor(N));M=np.zeros((n,n));start=N*(N+1)//2
    for i in range(start,n):
        M[i,i]=float((lam/kappa)**2/2)
        if i+1<n:M[i,i+1]=M[i+1,i]=float((lam/kappa)**2/4)
    hi=min(eigh(a,eigvals_only=True,subset_by_index=[0,0])[0],tail-1e-6);lo=0.
    if hi<=0:return dict(kappa=str(kappa),e='0',N=N)
    for _ in range(34):
        mid=(lo+hi)/2
        lowest=eigh(a-mid*np.eye(n)-M/(tail-mid),eigvals_only=True,subset_by_index=[0,0],check_finite=False)[0]
        if lowest>0:lo=mid
        else:hi=mid
    e=F(math.floor(lo*float(kappa)*10**6)-2,10**6)
    neg,piv=su.interval_inertia(N,lam/kappa,e/kappa,schur=True)
    if neg or any(x<=0 for x,y in piv):raise ArithmeticError('Inner numerical proposal did not certify')
    return dict(kappa=str(kappa),e=str(e),N=N)

def propose(names,couplings):
    import numpy as np
    from scipy.linalg import eigh
    targets=[];failures=[]
    for name in names:
        m,d=sg.calculate(name);n=len(m['energies']);M=np.array(d['M'],float);mass={e:np.array(v,float)for e,v in d['masses'].items()};I=np.eye(n)
        for lam in couplings:
            A=np.array(retained(m,d,lam),float);ev=eigh(A,eigvals_only=True);r=F(math.ceil(ev[0]*10**6)+2,10**6)
            for allocation in('bare','allocated'):
                for mode in('scalar_floor','resolved'):
                    best=None
                    ss=[F(1)]if allocation=='bare'else[F(k,20)for k in range(1,20)]
                    for s in ss:
                        local=[]if s==1 else[local_proposal(lam,(1-s)*coef)for coef in allocation_coeffs(m)]
                        offset=sum((F(x['e'])for x in local),F(0));floor=s*m['tail']+offset
                        lo=float(r)+1e-5;hi=min(float(floor)-1e-5,float(ev[1])-1e-6)
                        if lo>=hi:continue
                        def second(z):
                            corr=float(lam)**2*M/(float(floor)-z)if mode=='scalar_floor'else sum((float(lam)**2*mm/(float(s*e+offset)-z)for e,mm in mass.items()),np.zeros_like(A))
                            return eigh(A-z*I-corr,eigvals_only=True,subset_by_index=[1,1],check_finite=False)[0]
                        if second(lo)<=0:continue
                        for _ in range(32):
                            mid=(lo+hi)/2
                            if second(mid)>0:lo=mid
                            else:hi=mid
                        z=F(math.floor(lo*10**6)-2,10**6)
                        t=dict(model=name,lambda_=str(lam),alpha='1',mode=mode,allocation=allocation,s=str(s),r=str(r),z=str(z),d=str(floor),local_floors=local)
                        t['lambda']=t.pop('lambda_')
                        if z>r and(best is None or z>F(best['z'])):best=t
                    if best:
                        check=validate_target(best);targets.append(best);print(name,lam,allocation,mode,check['gap_display'],flush=True)
                    else:failures.append(dict(model=name,lambda_=str(lam),allocation=allocation,mode=mode,status='NO_CERTIFICATE_IN_DECLARED_GRID'));print(name,lam,allocation,mode,'INCONCLUSIVE',flush=True)
    return targets,failures

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--propose',action='store_true');ap.add_argument('--models',nargs='+',default=['two','strip','corner']);ap.add_argument('--couplings',nargs='+',default=['1/10','1/2','1','2','3','4','5']);ap.add_argument('--targets',type=Path,default=ROOT/'spatial_targets.json');ap.add_argument('--out',type=Path,default=Path('spatial_certificates.json'));a=ap.parse_args();start=time.monotonic()
    if not __debug__:raise RuntimeError('Do not run with -O')
    if a.propose:
        targets,fail=propose(a.models,list(map(F,a.couplings)));a.targets.write_text(json.dumps(targets,indent=2)+'\n');a.targets.with_name(a.targets.stem+'_inconclusive.json').write_text(json.dumps(fail,indent=2)+'\n')
    targets=json.loads(a.targets.read_text());rows=[validate_target(t)for t in targets]
    out=dict(certificates=rows,accepted_targets=len(rows),outer_inertia_tasks=3*len(rows),outer_pivot_signs=sum(3*r['dimension']for r in rows),inner_inertia_tasks=sum(len(r['local_floor_certificates'])for r in rows),inner_pivot_signs=sum(len(t['pivots'])for r in rows for t in r['local_floor_certificates']),seconds=time.monotonic()-start)
    a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(out,indent=2)+'\n');print('Accepted',len(rows),'seconds',out['seconds'])
if __name__=='__main__':main()
