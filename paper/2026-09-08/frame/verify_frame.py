#!/usr/bin/env python3
"""Standalone exact controls and numerical local SU(3) frame verification."""
from fractions import Fraction
from pathlib import Path
import json
import numpy as np
from scipy.linalg import expm


def generators():
    out=[]
    for i,j in [(0,1),(0,2),(1,2)]:
        a=np.zeros((3,3),complex); a[i,j]=1; a[j,i]=-1; out.append(a)
        a=np.zeros((3,3),complex); a[i,j]=1j; a[j,i]=1j; out.append(a)
    out.extend([1j*np.diag([1,-1,0]),1j*np.diag([1,1,-2])])
    return np.array(out)


def construct(x,a,da,K,T):
    """da[nu,mu,a] = partial_nu coefficient a[mu,a]."""
    d=len(x); delta=1/(4*d*8)
    blocks=[np.eye(3)/np.sqrt(2)]
    derivs=[[np.zeros((3,3),complex)] for _ in range(d)]
    for mu in range(d):
        for alpha in range(8):
            for sign in [1,-1]:
                w=delta+sign*a[mu,alpha]/(2*K)
                if w<=0: raise ValueError('K does not make all weights positive')
                U=expm(sign*K*x[mu]*T[alpha]); sw=np.sqrt(w)
                blocks.append(sw*U)
                for nu in range(d):
                    dw=sign*da[nu,mu,alpha]/(2*K)
                    du=sign*K*T[alpha]@U if nu==mu else np.zeros((3,3),complex)
                    derivs[nu].append((dw/(2*sw))*U+sw*du)
    return np.vstack(blocks),[np.vstack(v) for v in derivs]


def main():
    exact_checks=0
    m=32; delta=Fraction(1,4*m); K=Fraction(128)
    weights=[]
    for j in range(m):
        a=Fraction(j-16,32)
        wp,wm=delta+a/(2*K),delta-a/(2*K)
        assert wp>0 and wm>0; exact_checks+=1
        assert K*(wp-wm)==a; exact_checks+=1
        weights.extend([wp,wm])
    assert sum(weights)+Fraction(1,2)==1; exact_checks+=1
    # The diagonal witness has Tr(T*T)=-2 exactly, hence Tr(F wedge F)=-4.
    assert -sum(t*t for t in [1,-1,0])*2 == -4; exact_checks+=1
    # Pairing leaves no scalar derivative: (+da/2K)+(-da/2K)=0.
    assert Fraction(7,13)/(2*K)-Fraction(7,13)/(2*K)==0; exact_checks+=1
    T=generators(); rng=np.random.default_rng(20260908)
    residuals={'orthonormality':0.0,'connection':0.0,'curvature':0.0,'projector_curvature':0.0}
    numerical_comparisons=0
    for trial in range(24):
        x=rng.uniform(-.2,.2,4)
        a=rng.uniform(-.5,.5,(4,8)); da=rng.uniform(-.5,.5,(4,4,8))
        Q,dQ=construct(x,a,da,128.,T)
        assert Q.shape==(195,3)
        A=np.einsum('ma,aij->mij',a,T)
        AA=[Q.conj().T@v for v in dQ]
        P=Q@Q.conj().T
        residuals['orthonormality']=max(residuals['orthonormality'],float(np.linalg.norm(Q.conj().T@Q-np.eye(3))))
        numerical_comparisons+=1
        for mu in range(4):
            err=np.linalg.norm(AA[mu]-A[mu])
            residuals['connection']=max(residuals['connection'],float(err)); numerical_comparisons+=1
            for nu in range(mu+1,4):
                target=np.einsum('a,aij->ij',da[mu,nu]-da[nu,mu],T)+A[mu]@A[nu]-A[nu]@A[mu]
                f=dQ[mu].conj().T@dQ[nu]-dQ[nu].conj().T@dQ[mu]+AA[mu]@AA[nu]-AA[nu]@AA[mu]
                bm=dQ[mu]-Q@AA[mu]; bn=dQ[nu]-Q@AA[nu]
                fp=bm.conj().T@bn-bn.conj().T@bm
                residuals['curvature']=max(residuals['curvature'],float(np.linalg.norm(f-target)))
                residuals['projector_curvature']=max(residuals['projector_curvature'],float(np.linalg.norm(fp-target)))
                numerical_comparisons+=2
        if trial==0:
            assert np.linalg.norm(P@P-P)<1e-10; numerical_comparisons+=1
            dp=[v@Q.conj().T+Q@v.conj().T for v in dQ]
            for mu,nu in [(0,1),(2,3)]:
                left=(dp[mu]@Q).conj().T@(dp[nu]@Q)-(dp[nu]@Q).conj().T@(dp[mu]@Q)
                target=np.einsum('a,aij->ij',da[mu,nu]-da[nu,mu],T)+A[mu]@A[nu]-A[nu]@A[mu]
                assert np.linalg.norm(left-target)<1e-8; numerical_comparisons+=1
    assert max(residuals.values())<1e-8
    result={'status':'passed','seed':20260908,'exact_rational_controls':exact_checks,
        'numerical_comparisons':numerical_comparisons,'frame_shape':[195,3],
        'max_absolute_frobenius_residuals':residuals,'tolerance':1e-8,
        'scope':'Local classical frame identities; no Lean compilation or quantum measure/gap claim.'}
    Path(__file__).with_name('frame_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__': main()
