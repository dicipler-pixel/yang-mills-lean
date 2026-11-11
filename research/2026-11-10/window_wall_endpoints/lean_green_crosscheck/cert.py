"""Certified forward-secant slope bound for the window wall (round five), strip & corner at lam=5.
g(k,lam) = k*E(lam/k), E(mu) = ground energy of C2 + mu*(3 - Re chi) on SU(3) class functions.
Upper: exact Rayleigh quotient of a rational trial vector on levels <= N.
Lower: E >= z if  A - z - mu^2/(cQ - z) * P_N  is PSD (exact rational LDL), where cQ = min C2 on level N+1,
       ||B|| <= mu by Schur test (<=2 up / <=2 down neighbours, entries mu/2), potential block >= 0."""
from fractions import Fraction as F
import numpy as np, sys, time, json
N=int(sys.argv[1]) if len(sys.argv)>1 else 16
st=[(p,s-p) for s in range(N+1) for p in range(s+1)]; ix={t:i for i,t in enumerate(st)}; n=len(st)
def c2(p,q): return F(p*p+q*q+p*q+3*p+3*q,3)
nb={}
for (p,q),i in ix.items():
  nb[i]=[ix[t] for t in ((p+1,q),(p-1,q+1),(p,q-1),(p,q+1),(p+1,q-1),(p-1,q)) if t in ix]
cQ=min(c2(p,N+1-p) for p in range(N+2))
boundary=[ix[(p,N-p)] for p in range(N+1)]
def fmat(mu):
  M=np.zeros((n,n))
  for (p,q),i in ix.items():
    M[i,i]=float(c2(p,q))+3*mu
    for j in nb[i]: M[i,j]=-mu/2
  return M
def upper(mu):
  w,v=np.linalg.eigh(fmat(float(mu))); x=[F(round(a*10**12)) for a in v[:,0]]
  num=F(0); den=F(0)
  for (p,q),i in ix.items():
    xi=x[i]
    if xi==0: continue
    den+=xi*xi
    hx=(c2(p,q)+3*mu)*xi - mu/2*sum(x[j] for j in nb[i])
    num+=xi*hx
  return num/den, w[0]
def psd(mu,z):
  # exact LDL^T on banded matrix (ordered by level); returns True iff all pivots > 0
  pen=mu*mu/(cQ-z); bset=set(boundary)
  rows=[dict() for _ in range(n)]
  for (p,q),i in ix.items():
    rows[i][i]=c2(p,q)+3*mu-z-(pen if i in bset else 0)
    for j in nb[i]: rows[i][j]=-mu/2
  for k in range(n):
    d=rows[k].get(k,F(0))
    if d<=0: return False
    col=[(j,v) for j,v in rows[k].items() if j>k]
    for a,(i,vi) in enumerate(col):
      f=vi/d
      ri=rows[i]
      for j,vj in col:
        if j>=i:
          ri[j]=ri.get(j,F(0))-f*vj
          if j>i: rows[j][i]=ri[j]
  return True
def lower(mu,approx):
  # rational z just below the float ground value, backed off until certified
  for back in [1e-9,1e-8,1e-7,1e-6,1e-5,1e-4]:
    z=F(round((approx-back)*10**10),10**10)
    if z<cQ and psd(mu,z): return z
  return None
lam=F(5); h=F(1,100) if len(sys.argv)<3 else F(sys.argv[2])
cases={'strip':[F(7,2),F(3),F(7,2)],'corner':[F(3),F(3),F(3)]}
res={}
t0=time.time()
for name,co in cases.items():
  tot=F(0); detail=[]
  for c in set(co):
    mu_c=lam/c; mu_h=lam/(c+h)
    up,_=upper(mu_c); gup=c*up
    _,wf=upper(mu_h); lo=lower(mu_h,wf)
    assert lo is not None, (name,c)
    glo=(c+h)*lo
    sec=(glo-gup)/h
    detail.append(dict(c=str(c),g_up_c=float(gup),g_low_c_plus_h=float(glo),secant_lower=float(sec)))
    tot+=co.count(c)*c*sec
  slope_up=F(28,3)-tot
  res[name]=dict(N=N,h=str(h),sum_c_secant=float(tot),certified_slope_upper=float(slope_up),
                 slope_upper_exact=str(slope_up) if len(str(slope_up))<200 else None,excluded=slope_up<=0,detail=detail)
  print(name,'N',N,'h',h,'sum c*secant >=',float(tot),'=> W\'(0) <=',float(slope_up),'EXCLUDED' if slope_up<=0 else 'not certified', f'{time.time()-t0:.1f}s')
json.dump(res,open(f'cert_N{N}.json','w'),indent=1)
