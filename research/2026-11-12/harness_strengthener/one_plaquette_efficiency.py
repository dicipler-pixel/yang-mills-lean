#!/usr/bin/env python3
# SCRIPT: ONE_PLAQUETTE_EFFICIENCY
"""Scalar-norm versus matrix (boundary Gram) Schur certificate for ONE SU(3) plaquette, as a function of the
character cutoff N.  FLOATS ONLY: this is a comparison table, not a certificate.

    H = C2 + lam (3 - Re chi_(1,0)),  character basis (p,q), p+q <= N:
    diagonal c(p,q) + 3 lam, off-diagonal -lam/2 to the six neighbours,
    hidden floor d_N = ((N+1)^2 - floor((N+1)^2/4) + 3(N+1))/3,
    coupling Gram M on the shell p+q = N: diagonal lam^2/2, adjacent off-diagonal lam^2/4.

scalar bound (paper section 4.1, with ||B|| <= b = lam):  (mu1 + d - sqrt((d-mu1)^2 + 4 b^2))/2 - mu0   (needs mu1 < d)
matrix bound (Theorem 3): sup { z < d : K_M(z) = A - z - M/(d-z) has exactly one negative eigenvalue } - mu0.
The number of negative eigenvalues of K_M(z) is nondecreasing in z, so the sup is found by bisection; the count is
a banded LDL pivot-sign count (no pivoting, high shells first).

Run:  OMP_NUM_THREADS=1 python3 one_plaquette_efficiency.py     (about 2 to 4 minutes)
"""
import os
os.environ.setdefault('OMP_NUM_THREADS', '1')
import sys, time, csv
import numpy as np
from scipy.linalg import eigvals_banded
from pathlib import Path

HERE = Path(__file__).resolve().parent


def cas(p, q): return (p * p + q * q + p * q + 3 * p + 3 * q) / 3.0
def floor_d(N): s = N + 1; return (s * s - (s * s) // 4 + 3 * s) / 3.0


def band(N, lam):
    """upper band storage W[i, k] = A[i, i+k] in DESCENDING shell order; returns W, bandwidth, shell-N index list."""
    st = [(p, s - p) for s in range(N, -1, -1) for p in range(s + 1)]
    ix = {x: i for i, x in enumerate(st)}; n = len(st); bw = N + 2
    W = np.zeros((n, bw + 1))
    for i, (p, q) in enumerate(st):
        W[i, 0] = cas(p, q) + 3 * lam
        for t in ((p + 1, q), (p - 1, q + 1), (p, q - 1), (p, q + 1), (p + 1, q - 1), (p - 1, q)):
            j = ix.get(t)
            if j is not None and j > i:
                assert j - i <= bw; W[i, j - i] = -lam / 2
    return W, bw, list(range(N + 1))          # shell N = the first N+1 states, ordered by p


_TRI = {}
def tri(m):
    if m not in _TRI:
        I, J = np.triu_indices(m); _TRI[m] = (I, J, J - I)
    return _TRI[m]


def neg_count(W, bw):
    """number of negative pivots of the unpivoted LDL of the banded symmetric matrix (W is overwritten)."""
    n = W.shape[0]; cnt = 0
    for k in range(n):
        dk = W[k, 0]
        if dk == 0.0: return n                 # treat as failure
        cnt += dk < 0
        m = min(bw, n - 1 - k)
        if m:
            row = W[k, 1:m + 1]
            I, J, D = tri(m)
            W[k + 1 + I, D] -= row[I] * row[J] / dk
    return cnt


def bounds(N, lam):
    W, bw, shell = band(N, lam); n = W.shape[0]; d = floor_d(N)
    ab = np.zeros((bw + 1, n))                       # LAPACK upper band storage
    for k in range(bw + 1): ab[bw - k, k:] = W[:n - k, k]
    mu = eigvals_banded(ab, select='i', select_range=(0, min(1, n - 1)))
    mu0, mu1 = mu[0], mu[1]
    scalar = (mu1 + d - np.sqrt((d - mu1) ** 2 + 4 * lam * lam)) / 2 - mu0 if mu1 < d else float('nan')
    def count(z):
        K = W.copy(); K[:, 0] -= z; f = lam * lam / (d - z)
        K[shell, 0] -= f / 2
        K[shell[:-1], 1] -= f / 4
        return neg_count(K, bw)
    lo, hi = mu0, min(d, mu1 + 1.0)
    if not (mu0 < d) or count(mu0 + 1e-9 * max(1.0, abs(mu0))) > 1: return mu0, mu1, d, scalar, float('nan')
    hi = min(d - 1e-12 * max(1.0, d), mu1 + 1e-9)    # K <= A - z: beyond mu1 there are two negative directions
    if count(hi) <= 1: lo = hi
    else:
        for _ in range(46):
            mid = (lo + hi) / 2
            if count(mid) <= 1: lo = mid
            else: hi = mid
    return mu0, mu1, d, scalar, lo - mu0


def main():
    t0 = time.time(); rows = []; summary = []
    for lam in (1.0, 10.0, 100.0):
        Wc, bwc, _ = band(100, lam); n = Wc.shape[0]; ab = np.zeros((bwc + 1, n))
        for k in range(bwc + 1): ab[bwc - k, k:] = Wc[:n - k, k]
        mu = eigvals_banded(ab, select='i', select_range=(0, 1)); gap = mu[1] - mu[0]
        print('lambda = %g : converged gap (N = 100, float) = %.9f' % (lam, gap), flush=True)
        first = {('scalar', f): None for f in (0.5, 0.9, 0.99)}; first.update({('matrix', f): None for f in (0.5, 0.9, 0.99)})
        firstpos = {'scalar': None, 'matrix': None}
        for N in range(3, 81):
            mu0, mu1, d, sc, mx = bounds(N, lam)
            rows.append((lam, N, (N + 1) * (N + 2) // 2, d, mu0, mu1, sc, mx, gap))
            for name, v in (('scalar', sc), ('matrix', mx)):
                if v == v:
                    if v > 0 and firstpos[name] is None: firstpos[name] = N
                    for f in (0.5, 0.9, 0.99):
                        if first[(name, f)] is None and v >= f * gap: first[(name, f)] = N
            if N in (3, 5, 10, 15, 20, 25, 30, 40, 50, 60, 80):
                print('  N = %2d  d = %9.3f  scalar = %12.6f  matrix = %12.6f' % (N, d, sc, mx), flush=True)
        summary.append((lam, gap, firstpos, first))
    with open(HERE / 'one_plaquette_efficiency.csv', 'w', newline='') as fh:
        w = csv.writer(fh); w.writerow(['lambda', 'N', 'dim', 'd_N', 'mu0', 'mu1', 'scalar_gap_bound', 'matrix_gap_bound', 'converged_gap'])
        for r in rows: w.writerow(['%g' % r[0], r[1], r[2]] + ['%.9f' % x for x in r[3:]])
    print('\nsmallest N (3..80) at which each bound reaches a fraction of the converged gap (- = not reached by N = 80)')
    print('lambda | converged gap | bound  | first > 0 | 50% | 90% | 99%')
    for lam, gap, fp, first in summary:
        for name in ('scalar', 'matrix'):
            g = lambda x: '-' if x is None else str(x)
            print('%6g | %13.6f | %s | %9s | %3s | %3s | %3s' % (lam, gap, name, g(fp[name]), g(first[(name, 0.5)]),
                                                                 g(first[(name, 0.9)]), g(first[(name, 0.99)])))
    a = [r for r in rows if r[0] == 100.0 and r[1] == 25][0]
    print('\nanchor lambda = 100, N = 25: scalar = %.4f (paper: -33.3376), matrix = %.6f (paper gap 19.360771)' % (a[6], a[7]))
    ok = abs(a[6] + 33.3376) < 1e-3 and abs(a[7] - 19.360771) < 1e-4
    print('anchor reproduced' if ok else 'ANCHOR NOT REPRODUCED', '; %.1f s' % (time.time() - t0))
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
