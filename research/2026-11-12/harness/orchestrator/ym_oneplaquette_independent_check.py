# SCRIPT: YM_ONEPLAQUETTE_INDEPENDENT_CHECK
# Independent of the repo code. Builds H = kappa*C2 + lam*(3 - Re chi_10) on SU(3) class
# functions in the character basis chi_{p,q}, truncated at p+q <= N, from the two stated
# rules only (Casimir formula, fundamental-character multiplication), and diagonalises.
# A truncation's eigenvalues are UPPER bounds on the true ones (min-max), and they converge
# downward as N grows, so the large-N gap is the number the certified LOWER bounds must sit under.
import numpy as np
def build(lam, N, kappa=1.0):
    idx = {}
    for p in range(N+1):
        for q in range(N+1-p):
            idx[(p,q)] = len(idx)
    n = len(idx); H = np.zeros((n,n))
    for (p,q),i in idx.items():
        H[i,i] = kappa*(p*p+q*q+p*q+3*p+3*q)/3.0 + 3*lam
        for (a,b) in [(p+1,q),(p-1,q+1),(p,q-1),(p,q+1),(p+1,q-1),(p-1,q)]:
            if (a,b) in idx: H[i,idx[(a,b)]] += -lam/2.0
    return H
cert = {0.1:1.2868372, 1:1.3401688, 10:5.6481431, 100:19.3607700}
for lam,c in cert.items():
    out=[]
    for N in (40,70,100):
        w = np.linalg.eigvalsh(build(lam,N))
        out.append(w[1]-w[0])
    print("lam=%-5s gap(N=40,70,100)= %.7f %.7f %.7f | certified lower bound %.7f | slack %.3e | harmonic 2*sqrt(lam)=%.3f"
          % (lam, out[0],out[1],out[2], c, out[2]-c, 2*np.sqrt(lam)))
# the scalar bound of section 4.1 at lam=100, N=25, b = lam
lam=100; N=25
w = np.linalg.eigvalsh(build(lam,N)); mu0,mu1 = w[0],w[1]
s=N+1; d = (s*s - (s*s)//4 + 3*s)/3.0
E1 = (mu1 + d - np.sqrt((d-mu1)**2 + 4*lam*lam))/2
print("scalar certificate at lam=100,N=25: mu0=%.6f mu1=%.6f d=%.6f  E1_lower - mu0 = %.8f" % (mu0,mu1,d,E1-mu0))
