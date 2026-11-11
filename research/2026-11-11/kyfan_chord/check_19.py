# Cross-check: spin-network solver restricted to electric <= 40/3 must reproduce the repo's 19-state retained pencil.
import sys, numpy as np, scipy.linalg as sl
import pathlib
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2] / 'yang_mills_2026_09_09' / 'scripts'))
import two_plaquette_19 as t19
from fractions import Fraction as F
import sn_theta as sn
n, herm, L = sn.levels(2, [0, 0.1, 1, 4], ECUT=40/3 + 1e-9, k=19)
print('states', n, 'herm', herm)
for lam, ev in zip([0, 0.1, 1, 4], L):
    g, a, m = t19.retained(F(lam).limit_denominator(100))
    G = np.array(g, float); A = np.array(a, float)
    ref = sl.eigh(A, G, eigvals_only=True)
    print(lam, 'max |diff| over all 19 levels =', np.abs(np.sort(ev) - ref).max(), ' E0,E1 =', ref[:2])
