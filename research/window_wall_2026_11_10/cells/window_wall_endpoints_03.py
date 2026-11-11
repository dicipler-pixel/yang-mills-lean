# SCRIPT: WINDOW_WALL_ENDPOINTS_03
"""Dump the exact rational endpoints behind every certified-excluded cell, per face,
so Lean can discharge  T <= sum_p c_p * L_p  by exact arithmetic.
L_p = (g_low(c_p + h) - g_up(c_p)) / h.  Acceptance is the repo's integer-interval inertia
(same tests as window_wall_certified_02). Kill: any cell excluded in 02 not excluded here."""
import sys, json
from fractions import Fraction as F
REPO=sys.argv[1]
for sub in ('scripts','cross_theorem/scripts','cross_theorem/native'):
    sys.path.insert(0, REPO+'/research/yang_mills_2026_09_09/'+sub)
import spatial_gauge as sg, spatial_certificates as sc
import importlib.util
spec=importlib.util.spec_from_file_location('w2','window_wall_certified_02.py')
# reuse bounds() without rerunning 02's main: copy its core
import numpy as np, su3_character_certificate as su
N=30; H=F(1,1000)
st=su.states(N); idx={s:i for i,s in enumerate(st)}
C2=np.array([float(su.casimir(p,q)) for p,q in st]); ADJ=np.zeros((len(st),len(st)))
for (p,q),i in idx.items():
    for t in su.neighbors(p,q):
        j=idx.get(t)
        if j is not None: ADJ[i,j]=1.0
def e0(mu): return float(np.linalg.eigvalsh(np.diag(C2+3*mu)-(mu/2)*ADJ)[0])
cache={}
def bounds(k,lam):
    if (k,lam) in cache: return cache[(k,lam)]
    mu=lam/k; e=e0(float(mu)); lo=F(int(e*10**9)-20,10**9); hi=F(int(e*10**9)+20,10**9)
    neg,piv=su.interval_inertia(N,mu,lo,schur=True); assert neg==0 and all(a>0 for a,b in piv)
    neg2,_=su.interval_inertia(N,mu,hi,schur=False); assert neg2>=1
    cache[(k,lam)]=(k*lo,k*hi); return cache[(k,lam)]
cells=[('two','8'),('strip','5'),('corner','5'),('cube','3'),('double_cube','2')]
out=[]
for name,lam_s in cells:
    lam=F(lam_s); coef=sc.allocation_coeffs(sg.model(name)); faces=[]; tot=F(0)
    for c in coef:
        glo=bounds(c+H,lam)[0]; ghi=bounds(c,lam)[1]; L=(glo-ghi)/H; tot+=c*L
        faces.append(dict(c=str(c),glo_c_plus_h=str(glo),ghi_c=str(ghi),L=str(L)))
    assert tot>=F(28,3), (name,lam_s,float(tot))
    out.append(dict(model=name,lam=lam_s,h=str(H),faces=faces,sum=str(tot),margin=str(tot-F(28,3))))
    print(name,lam_s,len(coef),'faces  sum c*L =',float(tot),' >= 28/3 by',float(tot-F(28,3)))
json.dump(out,open(sys.argv[2],'w'),indent=1)
