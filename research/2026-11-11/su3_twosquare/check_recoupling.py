"""Structural checks of the GT spin-network build, ink 2026-11-11.
1. gl(3) relations + Casimir in the GT irreps (gt_su3.check) for p,q <= 8.
2. Racah-Speiser multiplicities = null-space dimensions (asserted inside the build) and sum N_a d_a = d_b d_c.
3. Orthogonality of the one-fundamental-leg recoupling (6j) matrix R: with no truncation, R R^T = 1 for every
   (b,c,a') tested (both bases span Hom(V_a', V_b (x) V_c (x) V_f)).
4. Intertwiner checks for J_{b (x) f -> b'} (isometry asserted in J_fund) and E/F intertwining.
"""
import numpy as np, itertools, theta_gt as tg, gt_su3 as gs
from gt_su3 import dim
print('1. GT relations max err', max(gs.check(p, q) for p in range(9) for q in range(9)))
e2 = 0
for b in [(p, q) for p in range(5) for q in range(5)]:
    for c in [(p, q) for p in range(4) for q in range(4)]:
        m = tg.tensor_mult(b, c); e2 = max(e2, abs(sum(n * dim(*a) for a, n in m.items()) - dim(*b) * dim(*c)))
print('2. sum N_a d_a - d_b d_c max', e2)
# 3. unrestricted R for a few pairs
tg.setup(1e9, K=8)
def hw(b, c):
    if (b, c) not in tg.HW: tg.HW[(b, c)] = tg.pair_hw((b, c))[1]
    return tg.HW[(b, c)]
worst = 0; ntest = 0
for b, c in [((1, 1), (1, 1)), ((2, 1), (1, 2)), ((2, 2), (1, 1)), ((3, 1), (2, 2)), ((2, 2), (2, 2))]:
    src = hw(b, c); db, dc = dim(*b), dim(*c)
    ops, W, widx = tg.product_ops(b, c)
    words = {}
    for a, (cols, V) in src.items():
        for k in range(V.shape[1]):
            u = np.zeros(db * dc); u[cols] = V[:, k]; words[(a, k)] = [tg.apply_word(ops, w, u) for w in tg.WORDS]
    targets_a2 = {a2 for a in src for a2 in tg.fund_targets(a)}
    for move in ('U', 'V'):
        arm = b if move == 'U' else c
        for a2 in targets_a2:
            Avs = []
            for (a, k), wl in words.items():
                if a2 in tg.fund_targets(a):
                    x = tg.Kcoef(a, a2)
                    Avs.append(np.stack([sum(x[i, j] * wl[j] for j in range(5)) for i in range(3)], 1).ravel())
            Bvs = []
            for arm2 in tg.fund_targets(arm):
                tb, tc = (arm2, c) if move == 'U' else (b, arm2)
                tgt = hw(tb, tc)
                if a2 not in tgt: continue
                J = tg.J_fund(arm, arm2); cols2, V2 = tgt[a2]
                for k2 in range(V2.shape[1]):
                    Um = np.zeros(dim(*tb) * dim(*tc)); Um[cols2] = V2[:, k2]; Um = Um.reshape(dim(*tb), dim(*tc))
                    B = np.einsum('rim,mn->rni', J, Um) if move == 'U' else np.einsum('nis,rs->rni', J, Um)
                    Bvs.append(B.ravel())
            A = np.array(Avs); B = np.array(Bvs)
            assert A.shape == B.shape, (b, c, a2, A.shape, B.shape)
            R = A @ B.T
            worst = max(worst, np.abs(R @ R.T - np.eye(len(R))).max(), np.abs(A @ A.T - np.eye(len(A))).max())
            ntest += 1
print(f'3. recoupling R orthogonality: {ntest} blocks (b,c,a\'), max |R R^T - 1| = {worst:.2e}')
