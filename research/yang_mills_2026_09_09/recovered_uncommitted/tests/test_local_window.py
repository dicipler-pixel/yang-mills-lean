#!/usr/bin/env python3
"""Independent finite numerical controls of the local-window operator proof.

The chain is a FINITE U(1)-rotor analogue, not an SU(3) spatial simulation.
Dense random controls test only the stated projection/min-max algebra.
"""
from __future__ import annotations
import os
os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
os.environ.setdefault('OMP_NUM_THREADS','1')
import argparse,itertools,json,math,time
from pathlib import Path
import numpy as np
from scipy.linalg import eigh,expm


def rotor_chain(length,k,alpha,lam):
    states=np.array(list(itertools.product(range(-k,k+1),repeat=length)),dtype=int)
    loc={tuple(s):i for i,s in enumerate(states)};d=len(states)
    h=np.diag(alpha*np.sum(states*states,axis=1).astype(float));pot=[]
    for e in range(length-1):
        w=np.eye(d)*lam
        for i,s in enumerate(states):
            t=s.copy();t[e]+=1;t[e+1]-=1
            j=loc.get(tuple(t))
            if j is not None:w[i,j]-=lam/2;w[j,i]-=lam/2
        h+=w;pot.append(w)
    return states,h,pot


def eps(alpha,a,b,omega,n):
    es=[1.0]
    for k in range(n+1):
        delta=alpha*(k+1)**2-a-omega
        es.append(min(1.,b*es[-1]/delta) if delta>0 else 1.)
    return es


def spectral_norm(a):
    if not a.size:return 0.
    return float(np.sqrt(max(0.,np.linalg.eigvalsh(a.conj().T@a)[-1])))


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out',type=Path,default=Path('local_window_numerical_controls.json'))
    args=ap.parse_args();start=time.monotonic();count=0;rows=[];trialrows=[]
    def req(b,why):
        nonlocal count
        if not b:raise AssertionError(why)
        count+=1
    for length,k in [(2,4),(3,4)]:
      for lam in [0.,.1,.5,2.]:
        alpha=1.;states,h,ps=rotor_chain(length,k,alpha,lam)
        ev,vec=eigh(h,check_finite=False);e0=ev[0];gap=ev[1]-e0
        degree=[int(i>0)+int(i<length-1) for i in range(length)]
        for e in range(length):
            rest=h.copy()-np.diag(alpha*states[:,e]**2)
            for p in range(length-1):
                if e in (p,p+1):rest-=ps[p]
            ids=np.flatnonzero(states[:,e]==0)
            er=eigh(rest[np.ix_(ids,ids)],subset_by_index=[0,0],eigvals_only=True)[0]
            req(e0<=er+lam*degree[e]+1e-9,'Constant-link trial comparison')
            trialrows.append(dict(length=length,lambda_=lam,link=e,E0=float(e0),
                                  E_rest=float(er),trial_allowance=lam*degree[e]))
        for omega in [.3,1.5,4.]:
          selected=ev<=e0+omega+1e-10;r=vec[:,selected]
          for n in [0,1,2,3]:
            s=kk=0.;local=[]
            keep=np.all(np.abs(states)<=n,axis=1)
            x=r[keep,:];y=r[~keep,:]
            for e in range(length):
                a=b=lam*degree[e];es=eps(alpha,a,b,omega,n)
                q=np.abs(states[:,e])>n
                actual=spectral_norm(r[q,:]);s+=es[-1]**2;kk+=b*es[-2]*es[-1]
                req(actual<=es[-1]+2e-8,'Local spectral-subspace tail')
                # Direct comparison to the entire finite hidden compression.
                low=eigh(h[np.ix_(q,q)],subset_by_index=[0,0],eigvals_only=True)[0]
                req(low>=e0+alpha*(n+1)**2-a-1e-8,'Relative hidden floor')
                local.append(dict(link=e,bound=es[-1],actual=actual))
            actual_global=spectral_norm(y)**2
            req(actual_global<=s+2e-8,'Commuting-projector union bound')
            vkeep=h[np.ix_(keep,~keep)]
            # Cross form on the whole low-energy subspace, not just each eigenvector.
            cross=x.conj().T@vkeep@y
            cross_h=(cross+cross.conj().T)/2
            cross_norm=float(np.max(np.abs(np.linalg.eigvalsh(cross_h))))
            req(cross_norm<=kk+2e-8,'Local retained-support cross-form bound')
            row=dict(length=length,k=k,lambda_=lam,omega=omega,N=n,
                     full_dimension=len(h),low_window_dimension=r.shape[1],
                     compression_dimension=int(keep.sum()),S=s,K=kk,
                     measured_union=actual_global,cross_form=cross_norm,locals=local)
            if s<1:
                error=(omega*s+kk)/(1-s)
                mus=eigh(h[np.ix_(keep,keep)],eigvals_only=True)
                req(r.shape[1]<=len(mus),'Projection injectivity dimension')
                for j in range(r.shape[1]):
                    req(mus[j]>=ev[j]-1e-8,'Variational lower side')
                    req(mus[j]<=ev[j]+error+1e-8,'Local-window Ritz upper side')
                if len(mus)>=2:
                    bound=min(omega,mus[1]-mus[0]-error)
                    req(gap>=bound-1e-8,'Gap transfer without gap premise')
                    row.update(error=error,certified_formula_lower=float(bound),actual_gap=float(gap))
                else:
                    req(gap>omega-1e-8,'Rank-one cutoff excludes any excited state in window')
                    row.update(error=error,rank_one_window=True,actual_gap=float(gap))
            rows.append(row)
    # General finite projection lemma, independent dense implementation.
    rng=np.random.default_rng(20260909);dense=[];underestimated_rejected=0
    for case in range(100):
        d=12;m=7;j=2
        energy=np.r_[0.,.4,.4, np.arange(1,d-2,dtype=float)+.3]
        z=rng.normal(size=(d,d))+1j*rng.normal(size=(d,d));z=.04*(z-z.conj().T)
        u=expm(z);h=u@np.diag(energy)@u.conj().T
        r=u[:,:3];omega=.4;s=spectral_norm(r[m:,:])**2
        b=spectral_norm(h[:m,m:]);err=(omega*s+b*math.sqrt(s))/(1-s)
        mu=eigh(h[:m,:m],eigvals_only=True)
        req(mu[j]<=energy[j]+err+2e-10,'Dense complex Rayleigh-Ritz inequality')
        req(energy[1]>=min(omega,mu[1]-mu[0]-err)-2e-10,'Dense gap comparison')
        if mu[j]>energy[j]+1e-6:underestimated_rejected+=1
        dense.append(dict(S=s,global_B=b,error=err,ritz_shift=float(mu[j]-energy[j])))
    req(underestimated_rejected==100,'False zero-leakage control should fail in every dense example')
    payload=dict(numerical_checks=count,rotor_configurations=len(rows),
                 finite_rotor_analogue_only=True,large_SU3_lattice_simulated=False,
                 rotor_rows=rows,trial_rows=trialrows,dense_cases=dense,
                 zero_leakage_negative_controls=underestimated_rejected,
                 elapsed_seconds=time.monotonic()-start)
    args.out.parent.mkdir(parents=True,exist_ok=True);args.out.write_text(json.dumps(payload,indent=2)+'\n')
    print('Checks',count,'rotor configurations',len(rows),'dense controls',len(dense),
          'false zero-leakage rejected',underestimated_rejected,'seconds',payload['elapsed_seconds'])
    print('Output',args.out)

if __name__=='__main__':main()
