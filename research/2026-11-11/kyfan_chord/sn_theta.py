# Float spin-network solver for the SU(3) two-square cell (theta graph, arms 1,3,3), Green 2026-11-11.
# Reference ("exact") E0, E1 only. NOT part of any certificate.
# Gauge-fixed: U, V = the two plaquette holonomies; physical space = functions of (U,V) invariant under
# simultaneous conjugation = (+)_{b,c} End_G(V_b (x) V_c), F_Phi(U,V) = tr(Phi D^b(U) (x) D^c(V)).
#   electric  = 3 c(b) + 3 c(c) + c(a),  a = irreducible block of V_b (x) V_c (shared short arm)
#   magnetic  = lam (6 - Re Tr U - Re Tr V)
# (repo normalisation: retained form (E + 6 lam) G - lam S, S = Re Tr U + Re Tr V, alpha = 1.)
# Galerkin truncation: arms b, c with p+q <= K and electric <= ECUT, so truncated levels are upper bounds that
# decrease as the cutoff grows; convergence is checked by raising K/ECUT.
import numpy as np, itertools, functools, sys

def dim(p, q): return (p + 1) * (q + 1) * (p + q + 2) // 2
def cas(p, q): return (p * p + q * q + p * q + 3 * p + 3 * q) / 3

def e(i, j):
    m = np.zeros((3, 3)); m[i, j] = 1; return m
FUND = dict(E1=e(0, 1), E2=e(1, 2), F1=e(1, 0), F2=e(2, 1), H1=e(0, 0) - e(1, 1), H2=e(1, 1) - e(2, 2))
AFUND = {k: -v.T for k, v in FUND.items()}
OPS = ('E1', 'E2', 'F1', 'F2', 'H1', 'H2')

def kron_ops(A, B):
    da = A['H1'].shape[0]; db = B['H1'].shape[0]
    return {k: np.kron(A[k], np.eye(db)) + np.kron(np.eye(da), B[k]) for k in OPS}

def apply_word(ops, w, v):
    for letter in reversed(w): v = ops[letter] @ v
    return v

def gen_words(ops, u, d):
    """BFS words in F1,F2 from hw vector u; greedy independent; returns words and R (W = Q R)."""
    words = [()]; vecs = [u]; Q = [u / np.linalg.norm(u)]
    frontier = [()]
    while len(words) < d:
        nf = []
        for w in frontier:
            for L in ('F1', 'F2'):
                w2 = (L,) + w; x = apply_word(ops, w2, u)
                r = x - sum((q.conj() @ x) * q for q in Q)
                if np.linalg.norm(r) > 1e-7 * max(1, np.linalg.norm(x)):
                    words.append(w2); vecs.append(x); Q.append(r / np.linalg.norm(r)); nf.append(w2)
                    if len(words) == d: break
            if len(words) == d: break
        assert nf or len(words) == d, 'word generation stalled'
        frontier = nf
    W = np.array(vecs).T
    Rm = np.linalg.qr(W)[1]
    return words, Rm

def basis_from(ops, u, words, Rm):
    W = np.array([apply_word(ops, w, u) for w in words]).T
    return W @ np.linalg.inv(Rm)

@functools.lru_cache(maxsize=None)
def irrep(p, q):
    """standard orthonormal weight basis; returns rep matrices dict, words, R."""
    ops = {k: np.zeros((1, 1)) for k in OPS}; u = np.ones(1)
    for _ in range(p): ops = kron_ops(ops, FUND)
    for _ in range(q): ops = kron_ops(ops, AFUND)
    u = np.zeros(3 ** (p + q)); idx = 0
    for _ in range(p): idx = idx * 3 + 0
    for _ in range(q): idx = idx * 3 + 2
    u[idx] = 1
    words, Rm = gen_words(ops, u, dim(p, q))
    Bm = basis_from(ops, u, words, Rm)
    rho = {k: Bm.conj().T @ ops[k] @ Bm for k in OPS}
    assert np.allclose(Bm.conj().T @ Bm, np.eye(dim(p, q)), atol=1e-9)
    return rho, words, Rm

def hw_vectors(ops, wt):
    h1 = np.real(np.diag(ops['H1'])); h2 = np.real(np.diag(ops['H2']))
    assert np.allclose(ops['H1'], np.diag(np.diag(ops['H1'])))
    cols = np.where((np.abs(h1 - wt[0]) < 1e-9) & (np.abs(h2 - wt[1]) < 1e-9))[0]
    if len(cols) == 0: return []
    M = np.vstack([ops['E1'][:, cols], ops['E2'][:, cols]])
    _, s, vh = np.linalg.svd(M)
    null = [vh[i].conj() for i in range(len(cols)) if (i >= len(s) or s[i] < 1e-8)]
    out = []
    for nv in null:
        u = np.zeros(ops['H1'].shape[0], dtype=complex); u[cols] = nv; out.append(u)
    return out

@functools.lru_cache(maxsize=None)
def decompose(b, c):
    """V_b (x) V_c = (+) M_a (x) V_a; returns {a: [C_{a,k}]} with consistent bases of V_a within this product.
    Uses the standard bases of b, c."""
    ops = kron_ops(irrep(*b)[0], irrep(*c)[0])
    h1 = np.real(np.diag(ops['H1'])); h2 = np.real(np.diag(ops['H2']))
    wts = sorted({(int(round(x)), int(round(y))) for x, y in zip(h1, h2) if x > -0.5 and y > -0.5})
    out = {}; tot = 0
    for a in wts:
        hws = hw_vectors(ops, a)
        if not hws: continue
        d = dim(*a)
        if a in [(p, q) for p in range(12) for q in range(12) if p + q <= 5]:
            _, words, Rm = irrep(*a)          # standard basis of a (needed when a is used as an arm label)
        else:
            words, Rm = gen_words(ops, hws[0], d)
        Cs = [basis_from(ops, u, words, Rm) for u in hws]
        out[a] = Cs; tot += d * len(Cs)
    assert tot == ops['H1'].shape[0], ('decomposition incomplete', b, c, tot)
    return out

def check_intertwiner(b, c):
    ops = kron_ops(irrep(*b)[0], irrep(*c)[0]); err = 0
    for a, Cs in decompose(b, c).items():
        ra = irrep(*a)[0] if a[0] + a[1] <= 5 else None
        for C in Cs:
            err = max(err, np.abs(C.conj().T @ C - np.eye(C.shape[1])).max())
            if ra is not None:
                for k in OPS: err = max(err, np.abs(ops[k] @ C - C @ ra[k]).max())
    return err

def build(K, ECUT=1e9):
    reps = [(p, s - p) for s in range(K + 1) for p in range(s + 1)]
    states = []; index = {}
    for b in reps:
        for c in reps:
            dec = decompose(b, c)
            for a, Cs in dec.items():
                el = 3 * cas(*b) + 3 * cas(*c) + cas(*a)
                if el > ECUT + 1e-9: continue
                n = len(Cs)
                for k in range(n):
                    for l in range(n):
                        index[(b, c, a, k, l)] = len(states); states.append((b, c, a, k, l, el))
    D = len(states); S = np.zeros((D, D), dtype=complex)
    f, fb = (1, 0), (0, 1)
    for (b, c, a, k, l, el) in states:
        i = index[(b, c, a, k, l)]
        Cak = decompose(b, c)[a][k].reshape(dim(*b), dim(*c), dim(*a))
        Cal = decompose(b, c)[a][l].reshape(dim(*b), dim(*c), dim(*a))
        s_in = np.sqrt(dim(*b) * dim(*c) / dim(*a))
        for which in ('U', 'V'):
            for ff in (f, fb):
                arm = b if which == 'U' else c
                for arm2, Cp in decompose(arm, ff).items():
                    if arm2[0] + arm2[1] > K: continue
                    Cp = Cp[0].reshape(dim(*arm), 3, dim(*arm2))
                    if which == 'U':
                        Yk = np.einsum('xfJ,xca->Jcaf', Cp.conj(), Cak); Yl = np.einsum('xfJ,xca->Jcaf', Cp.conj(), Cal)
                        b2, c2 = arm2, c
                    else:
                        Yk = np.einsum('yfJ,byа->bJaf'.replace('а', 'a'), Cp.conj(), Cak); Yl = np.einsum('yfJ,bya->bJaf', Cp.conj(), Cal)
                        b2, c2 = b, arm2
                    for a2, C2s in decompose(b2, c2).items():
                        n2 = len(C2s)
                        Zk = [np.einsum('JcA,Jcaf->Aaf', C.reshape(dim(*b2), dim(*c2), dim(*a2)).conj(), Yk) for C in C2s]
                        Zl = [np.einsum('JcA,Jcaf->Aaf', C.reshape(dim(*b2), dim(*c2), dim(*a2)).conj(), Yl) for C in C2s]
                        s_out = np.sqrt(dim(*b2) * dim(*c2) / dim(*a2))
                        for k2 in range(n2):
                            for l2 in range(n2):
                                j = index.get((b2, c2, a2, k2, l2))
                                if j is None: continue
                                coef = np.sum(Zk[k2] * Zl[l2].conj()) / dim(*a2)
                                S[j, i] += 0.5 * coef * s_in / s_out
    E = np.array([s[5] for s in states])
    return states, E, S

def levels(K, lam_list, ECUT=1e9, k=3):
    states, E, S = build(K, ECUT)
    herm = np.abs(S - S.conj().T).max()
    out = []
    for lam in lam_list:
        H = np.diag(E + 6 * lam) - lam * S
        out.append(np.linalg.eigvalsh((H + H.conj().T) / 2)[:k])
    return len(states), herm, out

if __name__ == '__main__':
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    print('intertwiner check max err', max(check_intertwiner((1, 1), (1, 1)), check_intertwiner((2, 0), (1, 1))))
    n, herm, L = levels(K, [0, 1])
    print(K, n, herm, L)
