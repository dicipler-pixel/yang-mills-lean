"""One SU(3) plaquette, H = kappa C2 + lam (3 - Re chi_f) in the orthonormal character basis (p,q), ink 2026-11-11.
Diagonal kappa c(p,q) + 3 lam, six neighbours -lam/2 (repo / ledger convention). Cutoff p+q <= N, checked."""
import numpy as np, sys, scipy.sparse as sp, scipy.sparse.linalg as sla
def cas(p, q): return (p * p + q * q + p * q + 3 * p + 3 * q) / 3
def levels(kappa, lam, N=80, k=3):
    st = [(p, s - p) for s in range(N + 1) for p in range(s + 1)]; ix = {s: i for i, s in enumerate(st)}
    H = sp.lil_matrix((len(st),) * 2)
    for i, (p, q) in enumerate(st):
        H[i, i] = kappa * cas(p, q) + 3 * lam
        for t in ((p + 1, q), (p - 1, q + 1), (p, q - 1)):
            j = ix.get(t)
            if j is not None: H[i, j] -= lam / 2; H[j, i] -= lam / 2
    return np.sort(sla.eigsh(H.tocsr(), k=k, which='SA', tol=1e-13)[0])
if __name__ == '__main__':
    for lam in (8, 64, 256):
        a, b = levels(1, lam, 60), levels(1, lam, 90)
        print(f'kappa=1 lam={lam}: gap={b[1]-b[0]:.10f} (N60-N90 diff {abs((a[1]-a[0])-(b[1]-b[0])):.1e}) ratio to 2sqrt(lam) {(b[1]-b[0])/(2*np.sqrt(lam)):.5f}')
