"""Float spectra of the exact truncated matrices (reference only, not a certificate)."""
import sys, time, pickle
import numpy as np, scipy.linalg as sl
from fractions import Fraction as F
import ring, ham, matrices

def dense(X, n):
    A = np.zeros((n, n))
    for (i, j), v in X.items(): A[i, j] = float(v)
    return A

if __name__ == '__main__':
    L = int(sys.argv[1]); caps = [F(x) for x in sys.argv[2].split(',')]
    for cap in caps:
        for sec in (0, 1):
            t = time.time()
            D = ham.build(ring.ring_graph(L), sec, cap); M = matrices.assemble(D); n = M['n']
            G, AE, AB = dense(M['G'], n), dense(M['AE'], n), dense(M['AB'], n)
            out = []
            for lam in (0.25, 0.5, 1.0):
                w = sl.eigh(AE + lam*AB, G, eigvals_only=True)[:3]
                out.append((lam, w))
            print(f'L={L} cap={cap} sector={sec} nP={n} nQ1={len(D["states"])-n} symAB={matrices.check_symmetric(M["AB"])} t={time.time()-t:.1f}s', flush=True)
            for lam, w in out:
                print(f'   lam={lam}: E0={w[0]:.6f} E1={w[1]:.6f} E2={w[2]:.6f} gap={w[1]-w[0]:.6f}', flush=True)
