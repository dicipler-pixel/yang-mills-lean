"""SU(3) irreps in the Gelfand-Tsetlin basis (exact closed-form gl(3) generator formulas), ink 2026-11-11.

Irrep (p,q) = GT top row (p+q, q, 0). Returns sparse real matrices E1=E12, E2=E23 (raising), F1=E1^T, F2=E2^T
and the Dynkin weights (h1,h2) = (E11-E22, E22-E33) of every GT pattern. Verified by `check()`: all gl(3)
commutation relations, Serre relations, and the quadratic Casimir = c(p,q) on every irrep used.
"""
import numpy as np, scipy.sparse as sp, functools

def dim(p, q): return (p + 1) * (q + 1) * (p + q + 2) // 2
def cas(p, q): return (p * p + q * q + p * q + 3 * p + 3 * q) / 3.0

@functools.lru_cache(maxsize=None)
def irrep(p, q):
    m13, m23, m33 = p + q, q, 0
    pats = [(m12, m22, m11) for m12 in range(m23, m13 + 1) for m22 in range(m33, m23 + 1)
            for m11 in range(m22, m12 + 1)]
    idx = {t: i for i, t in enumerate(pats)}; n = len(pats); assert n == dim(p, q)
    r1, c1, v1, r2, c2, v2 = [], [], [], [], [], []
    top = (m13, m23, m33)
    l3 = [m13 - 0, m23 - 1, m33 - 2]                        # l_{3j} = m_{3j} - j + 1 (j from 1)
    for (m12, m22, m11), i in idx.items():
        # E12: m11 -> m11+1
        if m11 + 1 <= m12:
            c = np.sqrt((m12 - m11) * (m11 - m22 + 1)); j = idx[(m12, m22, m11 + 1)]
            r1.append(j); c1.append(i); v1.append(c)
        # E23: m_{2i} -> m_{2i}+1 , Molev normalised formula with l_{ki} = m_{ki} - i + 1
        l2 = [m12, m22 - 1]; l1 = [m11]
        for ii, new in ((0, (m12 + 1, m22, m11)), (1, (m12, m22 + 1, m11))):
            if new not in idx: continue
            num = -np.prod([l2[ii] - x for x in l3]) * np.prod([l2[ii] - x + 1 for x in l1])
            den = np.prod([(l2[ii] - l2[jj]) * (l2[ii] - l2[jj] + 1) for jj in range(2) if jj != ii])
            val = num / den
            assert val > -1e-12, val
            if val > 0:
                r2.append(idx[new]); c2.append(i); v2.append(np.sqrt(val))
    E1 = sp.csr_matrix((v1, (r1, c1)), shape=(n, n)); E2 = sp.csr_matrix((v2, (r2, c2)), shape=(n, n))
    e1 = np.array([t[2] for t in pats]); e2 = np.array([t[0] + t[1] - t[2] for t in pats])
    e3 = np.array([m13 + m23 + m33 - t[0] - t[1] for t in pats])
    W = np.stack([e1 - e2, e2 - e3], 1)
    top_i = int(np.where((W[:, 0] == p) & (W[:, 1] == q))[0][0])
    return dict(E1=E1, E2=E2, F1=E1.T.tocsr(), F2=E2.T.tocsr(), W=W, Ed=(e1, e2, e3), n=n, top=top_i)

def check(p, q):
    R = irrep(p, q); n = R['n']; e1, e2, e3 = [sp.diags(x.astype(float)) for x in R['Ed']]
    E12, E23 = R['E1'], R['E2']; E21, E32 = R['F1'], R['F2']
    E13 = E12 @ E23 - E23 @ E12; E31 = E32 @ E21 - E21 @ E32
    err = 0
    def d(A): return abs(A).max() if A.nnz else 0.0
    err = max(err, d(E12 @ E21 - E21 @ E12 - (e1 - e2)), d(E23 @ E32 - E32 @ E23 - (e2 - e3)))
    err = max(err, d(E13 @ E31 - E31 @ E13 - (e1 - e3)))
    err = max(err, d(E12 @ E32 - E32 @ E12), d(E23 @ E21 - E21 @ E23))      # [E12,E32]=0, [E23,E21]=0
    err = max(err, d(E12 @ E13 - E13 @ E12), d(E23 @ E13 - E13 @ E23))      # Serre
    # Casimir sum_ij E_ij E_ji - (1/3)(sum E_ii)^2  -> c(p,q) for su(3) with this normalisation
    Es = {(0, 1): E12, (1, 0): E21, (1, 2): E23, (2, 1): E32, (0, 2): E13, (2, 0): E31,
          (0, 0): e1, (1, 1): e2, (2, 2): e3}
    C = sum(Es[(i, j)] @ Es[(j, i)] for i in range(3) for j in range(3))
    tr = e1 + e2 + e3; C = C - (tr @ tr) / 3.0
    C2 = (C / 2).toarray()     # gl3 Casimir/2 = su(3) C2 with C2(fund)=4/3
    err = max(err, np.abs(C2 - cas(p, q) * np.eye(n)).max())
    return err

if __name__ == '__main__':
    print(max(check(p, q) for p in range(9) for q in range(9)))
