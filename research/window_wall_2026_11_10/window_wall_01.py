# SCRIPT: WINDOW_WALL_01
"""Does the C<=8 complete-tail certificate have a size limit that can be read
off before any search?

Claim under test (derived from the repo's own LOCAL_ENERGY_FLOORS.md):
  every accepted target has  r < z < d,  d = s*(28/3) + sum_p e_p(s),
  and the true ground energy obeys  E0 >= sum_p g(c_p, lam)   (allocation with s=0),
  where g(kappa, lam) is the exact one-plaquette ground energy of
  kappa*C2 + lam*(3 - Re chi) and c_p = sum over the face's links of 1/(faces on that link).
  Since r >= E0, the usable window obeys
        d - r  <=  W(s) := s*(28/3) - sum_p [ g(c_p,lam) - g((1-s)*c_p, lam) ].
  g is concave in kappa, so W is concave in s with W(0)=0, and by Hellmann-Feynman
        W'(0) = 28/3 - sum_p c_p * <C2>_p ,
  <C2>_p = electric expectation in the one-plaquette ground state at coupling lam/c_p.
  So: if  sum_p c_p <C2>_p >= 28/3  no certificate of this class exists at any s.

KILL CONDITIONS
  (a) if any of the 58 stored accepted targets has d - r > W(s) (beyond float slack),
      the derivation is wrong;
  (b) if W'(0) <= 0 on a graph and coupling where a stored target exists, the
      derivation is wrong.
This is an outer bound only: W uses a weak lower bound on E0, so the real class
can die earlier than the bound says. Passing (a),(b) does not prove a gap.
"""
import sys, json
from fractions import Fraction as F
import numpy as np

REPO = sys.argv[1]
sys.path.insert(0, REPO + '/research/yang_mills_2026_09_09/scripts')
sys.path.insert(0, REPO + '/research/yang_mills_2026_09_09/cross_theorem/scripts')
sys.path.insert(0, REPO + '/research/yang_mills_2026_09_09/cross_theorem/native')
import spatial_gauge as sg
import spatial_certificates as sc
from targets import all_targets

NCUT = 45
states = [(p, s - p) for s in range(NCUT + 1) for p in range(s + 1)]
index = {st: i for i, st in enumerate(states)}
C2 = np.array([(p*p + q*q + p*q + 3*p + 3*q) / 3 for p, q in states])
ADJ = np.zeros((len(states), len(states)))
for (p, q), i in index.items():
    for t in ((p+1, q), (p-1, q+1), (p, q-1), (p, q+1), (p+1, q-1), (p-1, q)):
        j = index.get(t)
        if j is not None:
            ADJ[i, j] = 1.0

def one_loop(mu):
    """ground energy and <C2> of C2 + mu*(3 - Re chi), cutoff NCUT (float)."""
    h = np.diag(C2 + 3 * mu) - (mu / 2) * ADJ
    w, v = np.linalg.eigh(h)
    return w[0], float(v[:, 0] ** 2 @ C2)

def g(kappa, lam):
    if kappa <= 0:
        return 0.0          # kappa -> 0: ground energy -> 0 (state concentrates at U=1)
    return kappa * one_loop(lam / kappa)[0]

out = {'cutoff_used_for_one_loop_floats': NCUT, 'rows': [], 'slopes': []}
worst = -1e9
targets = all_targets()
for name, rows in targets.items():
    m = sg.model(name)
    coef = [float(c) for c in sc.allocation_coeffs(m)]
    for t in rows:
        lam = float(F(t['lambda'])); s = float(F(t['s']))
        d = float(F(t['d'])); r = float(F(t['r']))
        W = s * 28 / 3 - sum(g(c, lam) - g((1 - s) * c, lam) for c in coef)
        slack = W - (d - r)
        worst = max(worst, -slack)
        out['rows'].append(dict(model=name, lam=t['lambda'], s=t['s'], mode=t['mode'],
                                window=d - r, bound=W, slack=slack))
print('KILL (a): largest violation of  d - r <= W(s)  over 58 stored targets =', worst)

print()
print('slope W\'(0) = 28/3 - sum_p c_p <C2>_p   (positive = class not excluded by this bound)')
print(f"{'graph':12s} {'faces':>5s} {'lam':>6s} {'sum c<C2>':>10s} {'slope':>9s}  stored target?")
have = {(n, t['lambda']) for n, rows in targets.items() for t in rows}
bad_b = 0
for name in targets:
    m = sg.model(name)
    coef = [float(c) for c in sc.allocation_coeffs(m)]
    for lam_s in ['1/10', '1/2', '1', '2', '3', '4', '5', '10']:
        lam = float(F(lam_s))
        tot = sum(c * one_loop(lam / c)[1] for c in coef)
        slope = 28 / 3 - tot
        stored = (name, lam_s) in have
        if stored and slope <= 0:
            bad_b += 1
        out['slopes'].append(dict(model=name, faces=len(coef), lam=lam_s, sum_c_C2=tot, slope=slope, stored=stored))
        print(f"{name:12s} {len(coef):5d} {lam_s:>6s} {tot:10.4f} {slope:9.4f}  {'yes' if stored else '-'}")
print('KILL (b): stored targets sitting where the slope is <= 0 =', bad_b)

print()
print('Periodic cubic lattice (every link in 4 faces, c_p = 1): largest face count P with P*<C2>(lam) < 28/3')
print(f"{'lam/alpha':>9s} {'<C2>':>10s} {'P_max':>10s} {'largest side L with 3L^3 <= P_max':>36s}")
cubic = []
for lam_s in ['1/20', '1/10', '1/5', '1/2', '1', '2', '4']:
    lam = float(F(lam_s)); c2 = one_loop(lam)[1]
    pmax = (28 / 3) / c2
    L = int((pmax / 3) ** (1 / 3))
    cubic.append(dict(lam=lam_s, C2=c2, P_max=pmax, L_max=L))
    print(f"{lam_s:>9s} {c2:10.6f} {pmax:10.1f} {L:36d}")
out['periodic_cubic'] = cubic
out['small_coupling_law'] = 'perturbative <C2> = (3/8) lam^2  ->  P_max ~ (224/9)/lam^2'
print('check of the small-coupling law at lam=1/20: <C2>/lam^2 =', one_loop(0.05)[1] / 0.05 ** 2, ' (3/8 = 0.375)')
json.dump(out, open(sys.argv[2], 'w'), indent=1)
