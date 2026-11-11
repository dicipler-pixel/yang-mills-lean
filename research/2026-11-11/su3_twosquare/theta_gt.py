"""SU(3) two-square cell (theta graph, arms 1,3,3) in a Gelfand-Tsetlin spin-network basis, ink 2026-11-11.

Same Hamiltonian and conventions as the repo 19-state cell and Green's sn_theta.py:
  H(lam) = E_el + lam (6 - Re Tr U - Re Tr V),  alpha = 1,
  physical space = (+)_{b,c} End_G(V_b (x) V_c),  F_Phi(U,V) = sqrt(d_b d_c/d_a) tr(Phi D^b(U) (x) D^c(V)),
  basis |b c a k l> with Phi = iota_{a,k} iota_{a,l}^T, k,l = multiplicity labels of a in b (x) c,
  electric E_el = 3 c(b) + 3 c(c) + c(a)   (c = SU(3) quadratic Casimir, c(1,0) = 4/3).
Multiplication by Tr U (Tr V) is computed through the SU(3) recoupling (6j) matrix with one fundamental leg,
  R[k,k'] = < (iota_{a,k} (x) 1) K_{a (x) f -> a'} hw ,  (J_{b (x) f -> b'} (x) 1_c) iota'_{a',k'} hw >,
evaluated on highest-weight vectors only. Irreps are built in the GT basis (gt_su3.py), CG/intertwiners
numerically (null spaces of raising operators), all real.
Truncation (Galerkin): keep states with E_el <= ECUT (optionally also arm p+q <= K). Nested subspaces, so every
truncated level is an upper bound on the exact level and decreases as ECUT grows.
"""
import os
os.environ.setdefault('OMP_NUM_THREADS','1'); os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
import numpy as np, scipy.sparse as sp, scipy.sparse.linalg as sla, functools, itertools, sys, time, os
from multiprocessing import Pool
from gt_su3 import irrep, dim, cas

FW = [(1, 0), (-1, 1), (0, -1)]          # weights of the fundamental GT states, checked below
A1, A2 = np.array([2, -1]), np.array([-1, 2])

def weight_index(W):
    d = {}
    for i, w in enumerate(map(tuple, W)): d.setdefault(w, []).append(i)
    return {w: np.array(v) for w, v in d.items()}

FUNDW = [tuple(w) for w in irrep(1, 0)['W']]
assert sorted(FUNDW) == sorted(FW)

@functools.lru_cache(maxsize=None)
def product_ops(b, c):
    Rb, Rc = irrep(*b), irrep(*c); Ib, Ic = sp.identity(Rb['n'], format='csr'), sp.identity(Rc['n'], format='csr')
    ops = {k: (sp.kron(Rb[k], Ic) + sp.kron(Ib, Rc[k])).tocsr() for k in ('E1', 'E2', 'F1', 'F2')}
    W = (Rb['W'][:, None, :] + Rc['W'][None, :, :]).reshape(-1, 2)
    return ops, W, weight_index(W)

def hw_vectors(ops, widx, lam_w, tol=1e-9):
    lam_w = tuple(lam_w)
    if lam_w not in widx: return np.zeros((0, 0)), None
    cols = widx[lam_w]
    M = sp.vstack([ops['E1'][:, cols], ops['E2'][:, cols]]).tocsr()
    rows = np.unique(M.nonzero()[0]); Md = M[rows].toarray() if len(rows) else np.zeros((0, len(cols)))
    if Md.shape[0] == 0: return np.eye(len(cols)), cols
    G = Md.T @ Md                                          # null space of the raising operators via the Gram
    w, Q = np.linalg.eigh(G)
    N = Q[:, w < 1e-8 * max(1.0, w.max())]                 # columns: orthonormal hw vectors (restricted to cols)
    # gap check: next eigenvalue must be clearly nonzero (raising-operator spectra are O(1))
    if N.shape[1] < len(w): assert w[N.shape[1]] > 1e-4, ('ill-separated null space', w[N.shape[1]])
    # canonical sign/basis: reduced echelon-ish rotation is unnecessary; any orthonormal basis is a valid k-label
    return N, cols

def tensor_mult(b, c):
    """dominant weights a and multiplicities N_bc^a via Racah-Speiser on GT weights."""
    from collections import Counter
    out = Counter()
    for (x, y) in map(tuple, irrep(*b)['W']):
        l = [c[0] + x + 1, c[1] + y + 1]; s = 1
        for _ in range(8):
            if l[0] < 0: l = [-l[0], l[0] + l[1]]; s = -s; continue
            if l[1] < 0: l = [l[0] + l[1], -l[1]]; s = -s; continue
            break
        if l[0] == 0 or l[1] == 0: continue
        out[(l[0] - 1, l[1] - 1)] += s
    return {a: n for a, n in out.items() if n}

def el(b, c, a): return 3 * cas(*b) + 3 * cas(*c) + cas(*a)

# ---------------- truncation ----------------
CFG = {}
def setup(ECUT, K=None):
    reps = [(p, q) for p in range(60) for q in range(60) if 3 * cas(p, q) <= ECUT + 1e-9 and (K is None or p + q <= K)]
    pairs = [(b, c) for b in reps for c in reps if 3 * cas(*b) + 3 * cas(*c) <= ECUT + 1e-9]
    CFG.update(ECUT=ECUT, K=K, reps=set(reps), pairs=pairs, pairset=set(pairs))

def keep(b, c, a):
    if (b, c) not in CFG['pairset']: return False
    return el(b, c, a) <= CFG['ECUT'] + 1e-9

# ---------------- pass 1: hw vectors per pair ----------------
def pair_hw(bc):
    b, c = bc; ops, W, widx = product_ops(b, c); out = {}
    for a, N in tensor_mult(b, c).items():
        if not keep(b, c, a): continue
        V, cols = hw_vectors(ops, widx, a)
        assert V.shape[1] == N, ('multiplicity mismatch', b, c, a, V.shape, N)
        out[a] = (cols, V)
    product_ops.cache_clear()
    return bc, out

HW = {}
INDEX = {}

# ---------------- intertwiners with the fundamental ----------------
@functools.lru_cache(maxsize=None)
def J_fund(b, b2):
    """isometric intertwiner V_{b2} -> V_b (x) V_f in GT bases, array (d_b, 3, d_b2)."""
    ops, W, widx = product_ops_f(b)
    R2 = irrep(*b2); n2 = R2['n']
    V, cols = hw_vectors(ops, widx, b2); assert V.shape[1] == 1
    X = np.zeros((ops['E1'].shape[0], n2)); t = R2['top']
    v = np.zeros(ops['E1'].shape[0]); v[cols] = V[:, 0]; X[:, t] = v
    # level-by-level: depth = n1+n2 with top - weight = n1 a1 + n2 a2
    W2 = R2['W']; diff = np.array(b2) - W2
    # solve n1*A1 + n2*A2 = diff
    Minv = np.linalg.inv(np.array([A1, A2]).T)
    nn = np.rint(diff @ Minv.T).astype(int); depth = nn.sum(1)
    widx2 = weight_index(W2); done = {tuple(W2[t])}
    F = {1: R2['F1'].toarray(), 2: R2['F2'].toarray()}
    Fp = {1: ops['F1'], 2: ops['F2']}
    for dpt in range(1, depth.max() + 1):
        ws = {tuple(W2[i]) for i in np.where(depth == dpt)[0]}
        for w in ws:
            S = widx2[w]; Cs, Ys = [], []
            for i, al in ((1, A1), (2, A2)):
                wp = tuple(np.array(w) + al)
                if wp not in widx2: continue
                for m in widx2[wp]:
                    Cs.append(F[i][S, m]); Ys.append(Fp[i] @ X[:, m])
            C = np.array(Cs).T; Y = np.array(Ys).T          # X_S C = Y
            XS = Y @ np.linalg.pinv(C)
            assert np.abs(XS @ C - Y).max() < 1e-9
            X[:, S] = XS
    assert np.abs(X.T @ X - np.eye(n2)).max() < 1e-9
    return X.reshape(irrep(*b)['n'], 3, n2)

@functools.lru_cache(maxsize=None)
def product_ops_f(b):
    Rb, Rf = irrep(*b), irrep(1, 0)
    ops = {k: (sp.kron(Rb[k], sp.identity(3)) + sp.kron(sp.identity(Rb['n']), Rf[k])).tocsr() for k in ('E1', 'E2', 'F1', 'F2')}
    W = (Rb['W'][:, None, :] + Rf['W'][None, :, :]).reshape(-1, 2)
    return ops, W, weight_index(W)

WORDS = [(), ('F1',), ('F2',), ('F1', 'F2'), ('F2', 'F1')]     # word (X,Y) means X(Y(v))
def apply_word(ops, w, v):
    for L in reversed(w): v = ops[L] @ v
    return v

@functools.lru_cache(maxsize=None)
def Kcoef(a, a2):
    """hw of a2 in V_a (x) V_f written as sum_i sum_w x[i,w] word_w(top_a) (x) f_i ; returns x (3,5)."""
    ops, W, widx = product_ops_f(a); Ra = irrep(*a)
    V, cols = hw_vectors(ops, widx, a2); assert V.shape[1] == 1
    v = np.zeros(ops['E1'].shape[0]); v[cols] = V[:, 0]; v = v.reshape(Ra['n'], 3)
    top = np.zeros(Ra['n']); top[Ra['top']] = 1
    Wm = np.array([apply_word(Ra, w, top) for w in WORDS]).T
    x = np.zeros((3, len(WORDS)))
    for i in range(3):
        sol = np.linalg.lstsq(Wm, v[:, i], rcond=None)[0]
        assert np.abs(Wm @ sol - v[:, i]).max() < 1e-10
        x[i] = sol
    return x

# ---------------- pass 2: Tr U / Tr V matrix elements from a source pair ----------------
def fund_targets(b):
    return [(b[0] + dx, b[1] + dy) for dx, dy in FW if b[0] + dx >= 0 and b[1] + dy >= 0]

def source_block(bc):
    b, c = bc; db, dc = dim(*b), dim(*c)
    ops, W, widx = product_ops(b, c); src = HW[bc]
    rows, cols_, vals = [], [], []
    # A vectors: for each source (a,k) and a' in a (x) f
    words = {}
    for a, (cols, V) in src.items():
        for k in range(V.shape[1]):
            u = np.zeros(db * dc); u[cols] = V[:, k]
            words[(a, k)] = [apply_word(ops, w, u) for w in WORDS]
    Avec = {}
    for (a, k), wl in words.items():
        for a2 in fund_targets(a):
            x = Kcoef(a, a2)
            A = np.stack([sum(x[i, j] * wl[j] for j in range(len(WORDS))) for i in range(3)], 1)  # (db*dc, 3)
            Avec[(a, k, a2)] = A.reshape(db, dc, 3)
    for move in ('U', 'V'):
        arm = b if move == 'U' else c
        for arm2 in fund_targets(arm):
            tb, tc = (arm2, c) if move == 'U' else (b, arm2)
            if (tb, tc) not in HW: continue
            J = J_fund(arm, arm2); tgt = HW[(tb, tc)]; dtb, dtc = dim(*tb), dim(*tc)
            for a2, (cols2, V2) in tgt.items():
                srcs = [(a, k) for a in src for k in range(src[a][1].shape[1]) if a2 in fund_targets(a)]
                if not srcs: continue
                Bs = []
                for k2 in range(V2.shape[1]):
                    Um = np.zeros(dtb * dtc); Um[cols2] = V2[:, k2]; Um = Um.reshape(dtb, dtc)
                    if move == 'U': B = np.einsum('rim,mn->rni', J, Um)
                    else: B = np.einsum('nis,rs->rni', J, Um)
                    Bs.append(B)
                for a in {s[0] for s in srcs}:
                    Na = src[a][1].shape[1]; N2 = V2.shape[1]
                    R = np.array([[np.sum(Avec[(a, k, a2)] * Bs[k2]) for k2 in range(N2)] for k in range(Na)])
                    fac = np.sqrt(dim(*arm) * dim(*a2) / (dim(*a) * dim(*arm2)))
                    for k, l in itertools.product(range(Na), repeat=2):
                        for k2, l2 in itertools.product(range(N2), repeat=2):
                            v = fac * R[k, k2] * R[l, l2]
                            if abs(v) > 1e-14:
                                rows.append(INDEX[(tb, tc, a2, k2, l2)]); cols_.append(INDEX[(b, c, a, k, l)]); vals.append(v)
    product_ops.cache_clear()
    return np.array(rows, dtype=np.int32), np.array(cols_, dtype=np.int32), np.array(vals)

def _init_worker(hw, cfg):
    HW.update(hw); CFG.update(cfg)

def build(ECUT, K=None, procs=8, verbose=True, lean=False):
    t0 = time.time(); setup(ECUT, K); HW.clear()
    # warm caches in parent (inherited by fork)
    for r in CFG['reps']: irrep(*r)
    with Pool(procs) as P:
        for bc, out in P.imap_unordered(pair_hw, CFG['pairs'], chunksize=4): HW[bc] = out
    t1 = time.time()
    states = []; index = INDEX; index.clear()
    for (b, c) in CFG['pairs']:
        for a, (cols, V) in HW[(b, c)].items():
            N = V.shape[1]
            for k in range(N):
                for l in range(N):
                    index[(b, c, a, k, l)] = len(states); states.append((b, c, a, k, l))
    E = np.array([el(s[0], s[1], s[2]) for s in states])
    # warm J and K caches in parent for all needed pairs
    for r in CFG['reps']:
        for r2 in fund_targets(r):
            if r2 in CFG['reps']: J_fund(r, r2)
    for (b, c) in CFG['pairs']:
        for a in HW[(b, c)]:
            for a2 in fund_targets(a): Kcoef(a, a2)
    product_ops_f.cache_clear()
    R_, C_, V_ = [], [], []
    with Pool(procs, initializer=None) as P:
        for rows, cols_, vals in P.imap_unordered(source_block, CFG['pairs'], chunksize=2):
            R_.append(rows); C_.append(cols_); V_.append(vals)
    D = len(states)
    r = np.concatenate(R_); del R_
    c = np.concatenate(C_); del C_
    v = np.concatenate(V_); del V_
    T = sp.csr_matrix((v, (r, c)), shape=(D, D)); del r, c, v
    if lean:
        if verbose: print(f'ECUT={ECUT} K={K} states={D} pairs={len(CFG["pairs"])} nnzT={T.nnz} '
                          f'hw {t1-t0:.1f}s total {time.time()-t0:.1f}s', flush=True)
        return states, E, None, T
    S = ((T + T.T) / 2).tocsr()
    if verbose: print(f'ECUT={ECUT} K={K} states={D} pairs={len(CFG["pairs"])} nnz={S.nnz} '
                      f'hw {t1-t0:.1f}s total {time.time()-t0:.1f}s', flush=True)
    return states, E, S, T

def levels(E, S, lam, k=4):
    D = len(E); H = sp.diags(E + 6 * lam) - lam * S
    if D <= 300:
        return np.linalg.eigvalsh(H.toarray())[:k]
    w = sla.eigsh(H, k=k, which='SA', tol=1e-12, maxiter=200000)[0]
    return np.sort(w)

def levels_T(E, T, lam, k=4):
    """lowest k levels of diag(E+6lam) - lam (T+T^T)/2 without forming S (memory-lean)."""
    D = len(E); d = E + 6 * lam; TT = T.T
    op = sla.LinearOperator((D, D), matvec=lambda x: d * x - 0.5 * lam * (T @ x + TT @ x), dtype=float)
    w = sla.eigsh(op, k=k, which='SA', tol=1e-12, maxiter=200000)[0]
    return np.sort(w)
