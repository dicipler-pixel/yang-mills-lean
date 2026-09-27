#!/usr/bin/env python3
"""Independent differential and sampled-Haar checks of the SU(3) theta basis.

Differential evaluation uses Gell-Mann generators, not the stored electric
matrix. Sampled integration is a numerical control, not a rational certificate.
"""
from __future__ import annotations
import os
os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
import sys,argparse,json,time
from pathlib import Path
import numpy as np
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import two_plaquette_19 as ex


def haar_su3(rng,n):
    z=rng.normal(size=(n,3,3))+1j*rng.normal(size=(n,3,3))
    q,r=np.linalg.qr(z);p=np.diagonal(r,axis1=1,axis2=2);q=q*(p/np.abs(p))[:,None,:]
    q[:,:,0]/=np.linalg.det(q)[:,None]
    return q


def generators():
    out=[]
    for i,j in [(0,1),(0,2),(1,2)]:
        t=np.zeros((3,3),complex);t[i,j]=t[j,i]=.5;out.append(t)
        t=np.zeros((3,3),complex);t[i,j]=-.5j;t[j,i]=.5j;out.append(t)
    out.append(np.diag([.5,-.5,0.]));out.append(np.diag([1.,1.,-2.])/(2*np.sqrt(3.)))
    return out


def multiply_jets(a,b):
    # Tuple (value, first derivative, second derivative).
    return (a[0]@b[0],a[1]@b[0]+a[0]@b[1],
            a[2]@b[0]+2*a[1]@b[1]+a[0]@b[2])


def scalar_jets(a,b):
    return a[0]*b[0],a[1]*b[0]+a[0]*b[1],a[2]*b[0]+2*a[1]*b[1]+a[0]*b[2]


def derivative(p,u,v,t,acted):
    ident=np.eye(3,dtype=complex);zero=np.zeros((3,3),complex);ans=0j
    for coef,product in p:
        result=(1.+0j,0j,0j)
        for word in product:
            jet=(ident,zero,zero)
            for name,sgn in word:
                a=u if name=='U' else v
                if name in acted:
                    if sgn==1:z=(a,1j*t@a,-t@t@a)
                    else:z=(a.conj().T,-1j*a.conj().T@t,-a.conj().T@t@t)
                else:z=(a if sgn==1 else a.conj().T,zero,zero)
                jet=multiply_jets(jet,z)
            result=scalar_jets(result,tuple(np.trace(x) for x in jet))
        ans+=float(coef)*result[2]
    return ans


def basis_values(u,v):
    a=np.trace(u,axis1=-2,axis2=-1);b=np.trace(v,axis1=-2,axis2=-1)
    r=np.trace(u@np.swapaxes(v.conj(),-1,-2),axis1=-2,axis2=-1)
    g=np.trace(u@v,axis1=-2,axis2=-1);f=a*b;mix=a*b.conj()
    bary=f-g;octet=mix-r/3;sextet=f+g
    u6=(a*a+np.trace(u@u,axis1=-2,axis2=-1))/2
    v6=(b*b+np.trace(v@v,axis1=-2,axis2=-1))/2
    return np.array([np.ones_like(a),a,a.conj(),b,b.conj(),r,r.conj(),
                     bary,bary.conj(),octet,octet.conj(),sextet,sextet.conj(),
                     np.abs(a)**2-1,np.abs(b)**2-1,u6,u6.conj(),v6,v6.conj()]).T


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--samples',type=int,default=100000)
    ap.add_argument('--out',type=Path,default=Path('su3_independent_controls.json'))
    args=ap.parse_args();start=time.monotonic();rng=np.random.default_rng(9032026)
    ts=generators();count=0
    if not np.allclose(sum(t@t for t in ts),np.eye(3)*4/3,atol=1e-14):
        raise AssertionError('Wrong Casimir generator normalization')
    count+=1;u=haar_su3(rng,24);v=haar_su3(rng,24);max_res=0.;wrong_res=0.
    for a,b,values in zip(u,v,basis_values(u,v)):
        for i,p in enumerate(ex.BASIS):
            cu=-sum(derivative(p,a,b,t,{'U'}) for t in ts)
            cv=-sum(derivative(p,a,b,t,{'V'}) for t in ts)
            cd=-sum(derivative(p,a,b,t,{'U','V'}) for t in ts)
            actual=3*cu+3*cv+cd;expected=float(ex.ENERGY[i])*values[i]
            residual=abs(actual-expected);max_res=max(max_res,residual)
            if residual>2e-10*(1+abs(expected)):
                raise AssertionError(('Electric eigenfunction',i,residual))
            count+=1
            if i in (5,6):wrong_res=max(wrong_res,abs(4*cu+4*cv-expected))
    if wrong_res<1.:raise AssertionError('Independent-plaquette false control did not separate')
    count+=1
    g,s,s2,m=ex.matrices();targets=list(map(lambda x:np.array(x,dtype=float),(g,s,s2)))
    sums=[np.zeros((19,19),complex) for _ in range(3)]
    second=[np.zeros((19,19)) for _ in range(3)]
    processed=0
    while processed<args.samples:
        k=min(2000,args.samples-processed);u=haar_su3(rng,k);v=haar_su3(rng,k)
        f=basis_values(u,v);w=np.real(f[:,1]+f[:,3])
        for order in range(3):
            z=f.conj()[:,:,None]*f[:,None,:]*(w**order)[:,None,None]
            sums[order]+=z.sum(axis=0);second[order]+=(np.abs(z)**2).sum(axis=0)
        processed+=k
    controls=[]
    for order in range(3):
        mean=sums[order]/processed
        se=np.sqrt(np.maximum(0.,second[order]/processed-np.abs(mean)**2)/processed)
        diff=np.abs(mean-targets[order]);standardized=diff/np.maximum(se,1e-12)
        # Fixed-seed numerical integration check; no confidence interval claim.
        if np.any(diff>8*se+1e-10):raise AssertionError('Sampled Haar control outside eight-SE diagnostic')
        controls.append(dict(matrix=['Gram','S','S2'][order],
                             max_absolute_difference=float(diff.max()),
                             max_standardized_difference=float(standardized.max()),
                             largest_standard_error=float(se.max())))
        count+=19*19
    payload=dict(checks=count,differential_samples=24,
                 maximum_electric_identity_residual=max_res,
                 independent_plaquette_false_model_residual=wrong_res,
                 Haar_sample_pairs=processed,Haar_controls=controls,
                 exact_Haar_certificate=False,elapsed_seconds=time.monotonic()-start)
    args.out.parent.mkdir(parents=True,exist_ok=True);args.out.write_text(json.dumps(payload,indent=2)+'\n')
    print(json.dumps(payload,indent=2))

if __name__=='__main__':main()
