# SCRIPT: YM_SCALAR_BOUND_VS_CUTOFF
# Question: is the scalar-norm certificate at lam=100 hopeless, or only too weak at N=25?
# Same formula as section 4.1 of the paper, b = lam, d = first omitted Casimir, for growing N.
# Also the matrix certificate's reach: smallest N at which K_M(z) (z just under the N=100 E1) has
# exactly one negative eigenvalue.
import numpy as np
def build(lam, N):
    idx={}
    for p in range(N+1):
        for q in range(N+1-p): idx[(p,q)]=len(idx)
    n=len(idx); H=np.zeros((n,n))
    for (p,q),i in idx.items():
        H[i,i]=(p*p+q*q+p*q+3*p+3*q)/3.0+3*lam
        for ab in [(p+1,q),(p-1,q+1),(p,q-1),(p,q+1),(p+1,q-1),(p-1,q)]:
            if ab in idx: H[i,idx[ab]]+=-lam/2.0
    return H,idx
lam=100.0
Hbig,_=build(lam,100); wb=np.linalg.eigvalsh(Hbig); E0,E1=wb[0],wb[1]
print('reference E0=%.6f E1=%.6f gap=%.6f'%(E0,E1,E1-E0))
for N in (15,20,25,30,40,50,60,80):
    H,idx=build(lam,N); w=np.linalg.eigvalsh(H); mu0,mu1=w[0],w[1]
    s=N+1; d=(s*s-(s*s)//4+3*s)/3.0
    scal=(mu1+d-np.sqrt((d-mu1)**2+4*lam*lam))/2-mu0
    # matrix certificate: shell Gram M, test z slightly below true E1
    n=len(idx); M=np.zeros((n,n))
    for (p,q),i in idx.items():
        if p+q==N:
            M[i,i]=lam*lam/2
            if (p-1,q+1) in idx: M[i,idx[(p-1,q+1)]]=lam*lam/4; M[idx[(p-1,q+1)],i]=lam*lam/4
    z=E1-1e-4
    neg = int((np.linalg.eigvalsh(H-z*np.eye(n)-M/(d-z))<0).sum()) if z<d else -1
    print('N=%2d dim=%4d d=%8.2f scalar gap bound=%10.4f | matrix K_M negatives at z=E1-1e-4: %s'%(N,n,d,scal,neg))
