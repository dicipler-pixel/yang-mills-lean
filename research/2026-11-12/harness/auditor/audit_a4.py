# SCRIPT: AUDIT_A4
# Independent end-to-end sanity check of the allocation inequality on two squares.
# No repo code is used. Standard library plus numpy.
#
# Why this check means something: the allocation argument says
#   H(two squares) >= h_1 + h_2, each h_p a one-plaquette operator with kappa = 7/2,
# so E0(two squares) >= 2 g(7/2), where g is the one-plaquette ground energy.
# g is computed here from the character recursion chi_3 chi_(p,q) = chi_(p+1,q)+chi_(p-1,q+1)+chi_(p,q-1).
# A second, fully independent sandwich uses no repo number at all: the seven-state trace basis
# 1, TrU, TrU*, TrV, TrV*, Tr(UV*), Tr(VU*) gives a Rayleigh-Ritz UPPER bound on E0, so
#   2 g(7/2) <= E0 <= E0(seven states) must hold if the inequality is right.
import sys
import numpy as np

def cas(p, q):
    return (p*p + q*q + p*q + 3*p + 3*q) / 3.0

def one_plaquette(kappa, lam, N):
    idx = {}
    for p in range(N + 1):
        for q in range(N + 1 - p):
            idx[(p, q)] = len(idx)
    H = np.zeros((len(idx), len(idx)))
    for (p, q), i in idx.items():
        H[i, i] = kappa * cas(p, q) + 3.0 * lam
        for nb in ((p + 1, q), (p - 1, q), (p, q + 1), (p, q - 1), (p + 1, q - 1), (p - 1, q + 1)):
            if nb in idx:
                H[i, idx[nb]] = -lam / 2.0
    assert np.allclose(H, H.T)
    return np.linalg.eigvalsh(H)

def haar_su3(rng, n):
    z = (rng.standard_normal((n, 3, 3)) + 1j * rng.standard_normal((n, 3, 3))) / np.sqrt(2.0)
    q, r = np.linalg.qr(z)
    d = np.diagonal(r, axis1=1, axis2=2)
    q = q * (d / np.abs(d))[:, None, :]
    return q / (np.linalg.det(q) ** (1.0 / 3.0))[:, None, None]

def seven_state(lam):
    # orthonormal basis order: 1, u, u*, v, v*, r, r*  with u=TrU, v=TrV, r=Tr(U V^dagger)
    E = np.array([0.0, 16/3, 16/3, 16/3, 16/3, 8.0, 8.0])
    S = np.zeros((7, 7))          # matrix of multiplication by u+u*+v+v*
    def put(i, j, x):
        S[i, j] = S[j, i] = x
    for j in (1, 2, 3, 4):
        put(0, j, 1.0)            # <u|S|1> = int |TrU|^2 = 1
    put(1, 2, 1.0)                # <u|S|u*> = int (TrU*)^3 = 1 (one invariant in 3bar x 3bar x 3bar)
    put(3, 4, 1.0)
    put(5, 1, 1/3); put(5, 4, 1/3)   # <r|S|u> = int Tr(VU*) TrU TrV* = 1/3, same for <r|S|v*>
    put(6, 2, 1/3); put(6, 3, 1/3)
    return np.diag(E) + 6.0 * lam * np.eye(7) - (lam / 2.0) * S, S

def mc_check(S):
    # seeded Haar Monte Carlo check of the hand-derived Gram and S matrices (loose tolerance)
    rng = np.random.default_rng(20261112)
    n = 400000
    U, V = haar_su3(rng, n), haar_su3(rng, n)
    u = np.trace(U, axis1=1, axis2=2); v = np.trace(V, axis1=1, axis2=2)
    r = np.einsum('nij,nij->n', U, V.conj())
    f = np.array([np.ones(n, complex), u, u.conj(), v, v.conj(), r, r.conj()])
    s = 2.0 * (u.real + v.real)
    G = (f.conj() @ f.T) / n
    Sm = ((f.conj() * s) @ f.T) / n
    return np.abs(G - np.eye(7)).max(), np.abs(Sm - S).max()

def main():
    lam, kappa = 1.0, 3.5
    print('one-plaquette ground energy g(kappa=7/2, lambda=1) versus cutoff p+q <= N')
    g = {}
    for N in (10, 20, 40, 60):
        ev = one_plaquette(kappa, lam, N)
        g[N] = ev[0]
        print('  N = %2d  states %4d  g = %.12f  first excited = %.12f' % (N, (N + 1) * (N + 2) // 2, ev[0], ev[1]))
    g60 = g[60]
    print('  change N=40 -> 60: %.3e' % abs(g[60] - g[40]))
    # controls on the one-plaquette matrix
    ev0 = one_plaquette(kappa, 0.0, 12)
    assert abs(ev0[0]) < 1e-12 and abs(ev0[1] - kappa * 4 / 3) < 1e-12
    pert = 3.0 - 2 * 0.25 / (kappa * 4 / 3)     # second-order: 3*lam - 2*(lam/2)^2/(kappa*4/3)
    print('  second-order perturbative value 3 - 1/(2*kappa*4/3) = %.6f (control, order-of-magnitude control only; higher orders are ~1e-2)' % pert)
    E0_repo = 5.794723397655
    print()
    print('2*g(7/2)              = %.12f' % (2 * g60))
    print('repo E0 (ECUT 250)    = %.12f   margin = %.12f' % (E0_repo, E0_repo - 2 * g60))
    H7, S = seven_state(lam)
    e7 = np.linalg.eigvalsh(H7)
    gerr, serr = mc_check(S)
    print('own 7-state upper bound on E0 = %.12f   (Monte Carlo check of my Gram / S matrices: max dev %.4f / %.4f)' % (e7[0], gerr, serr))
    print('own 7-state E1 = %.12f, 7-state gap = %.12f (Galerkin value, not a bound on the gap)' % (e7[1], e7[1] - e7[0]))
    problems = []
    if not (abs(g[60] - g[40]) < 1e-10):
        problems.append('one-plaquette energy not converged in cutoff')
    if gerr > 0.02 or serr > 0.03:
        problems.append('my own 7-state matrices fail the Haar Monte Carlo check')
    if 2 * g60 > E0_repo:
        problems.append('2*g(7/2) = %.12f exceeds repo E0 %.12f' % (2 * g60, E0_repo))
    if 2 * g60 > e7[0]:
        problems.append('2*g(7/2) exceeds my own 7-state upper bound %.12f' % e7[0])
    if E0_repo > e7[0] + 1e-9:
        problems.append('repo E0 lies above my own variational upper bound %.12f' % e7[0])
    if problems:
        print('RESULT A4: KILLED — ' + ' | '.join(problems)); sys.exit(1)
    print('RESULT A4: SURVIVES')
main()
