# Try to reproduce GPT's double-cube test (b) (WINDOW_WALL.md, "GPT's separate test"):
#   U(lam) = 28/3 + (20541500575676903/909090909514080) lam   (alpha = 1)
#   compared with lambda_min of the 95 x 95 retained matrix, "gives 0.9867, certificate accepted at 0.5".
# The 95 x 95 matrix: spatial_certificates.retained(m, d, lam) for spatial_gauge model 'double_cube'
#   basis = 1 + 2 x (11 squares + 36 hexagons) = 95 Wilson-loop states, A = diag(E_i) + 3 P lam - lam S, P = 11.
# Exact S comes from dump_dcube.py (repo spatial_gauge.calculate) -> dcube_S.json.
# Floats only propose; the bracket is accepted by the repo's exact integer-interval LDL (spatial_certificates.interval_inertia).
import sys, os, json
from fractions import Fraction as F
from pathlib import Path
import numpy as np
HERE = Path(__file__).resolve().parent
YM = os.environ.get('YM_RESEARCH', str(HERE.parents[1] / 'research' / 'yang_mills_2026_09_09'))
for p in ('/scripts', '/cross_theorem/scripts', '/cross_theorem/native'): sys.path.insert(0, YM + p)
import spatial_certificates as sc
from targets import all_targets

D = json.load(open(HERE / 'dcube_S.json'))
n, P = D['n'], D['P']; En = [F(x) for x in D['energies']]; S = [[F(x) for x in r] for r in D['S']]
assert n == 95 and P == 11
K = F(20541500575676903, 909090909514080)
def U(lam): return F(28, 3) + K * lam
def A(lam): return [[(En[i] + 3 * P * lam if i == j else F(0)) - lam * S[i][j] for j in range(n)] for i in range(n)]
Sf = np.array(S, float); Ef = np.array([float(e) for e in En])
def evals(lam): return np.linalg.eigvalsh(np.diag(Ef + 3 * P * lam) - lam * Sf)
def lmin(lam): return evals(lam)[0]
def neg_count(lam, shift):   # exact: number of negative pivots of A(lam) - shift I
    a = A(lam); a = [[a[i][j] - (shift if i == j else 0) for j in range(n)] for i in range(n)]
    return sc.interval_inertia(a)[0]

print(f'dimension {n}, plaquettes {P}, 3P = {3*P}; U slope K = {float(K):.15f} = 3P - {float(3*P - K):.12f}')
print(f'S spectrum: max {np.linalg.eigvalsh(Sf)[-1]:.10f}, min {np.linalg.eigvalsh(Sf)[0]:.10f}')
out = {}
# stored accepted double-cube target(s): consistency with this matrix
for t in all_targets().get('double_cube', []):
    if t['model'] == 'double_cube':
        lam = F(t['lambda']); r, d = F(t['r']), F(t['d'])
        print(f"stored target lam={t['lambda']} {t['allocation']}/{t['mode']} s={t['s']}: r={float(r):.6f}  lambda_min(A)={lmin(float(lam)):.6f}"
              f"  d={float(d):.6f}  U(lam)={float(U(lam)):.6f}  d<=U: {d <= U(lam)}  lambda_min<U: {lmin(float(lam)) < float(U(lam))}")

# Reading 1: crossing lambda_min(A(lam)) = U(lam). Above it no r with A - r I having one negative direction can sit below
# any omitted-sector floor d <= U(lam) (trial state), so no C<=8 certificate exists.
f = lambda l: lmin(l) - float(U(F(l)))
grid = [0.1, 0.25, 0.5, 0.75, 0.9, 0.95, 0.98, 0.9867, 1.0, 1.25, 1.5, 2.0, 3.0]
print('lam, lambda_min(A), U(lam), lambda_min - U, ratio lambda_min/U')
for l in grid:
    print(f'  {l:<7} {lmin(l):12.6f} {float(U(F(l))):12.6f} {f(l):+12.6f} {lmin(l)/float(U(F(l))):.6f}')
roots = [ (a, b) for a, b in zip(np.linspace(0.01, 5, 500)[:-1], np.linspace(0.01, 5, 500)[1:]) if f(a) * f(b) < 0]
print('sign changes of lambda_min - U on (0.01, 5]:', [(round(a, 4), round(b, 4)) for a, b in roots])
res = []
for a, b in roots:
    for _ in range(60):
        m = (a + b) / 2
        if f(a) * f(m) <= 0: b = m
        else: a = m
    lf = (a + b) / 2
    lo, hi = F(round(lf * 10**6) - 1, 10**6), F(round(lf * 10**6) + 1, 10**6)
    nlo, nhi = neg_count(lo, U(lo)), neg_count(hi, U(hi))
    print(f'Reading 1 crossing lam* ~ {lf:.9f}; exact LDL: neg pivots of A-U at {float(lo)} = {nlo}, at {float(hi)} = {nhi}')
    # controls: the claimed state at each end must flip if we use the wrong end
    res.append(dict(lam_float=lf, lam_lo=str(lo), neg_at_lo=nlo, lam_hi=str(hi), neg_at_hi=nhi,
                    certified_bracket=(nlo >= 1 and nhi == 0) or (nlo == 0 and nhi >= 1)))
out['reading1_lambda_min_eq_U'] = res
# control: at 1/2 the test must NOT exclude (stored certificate accepted there)
c05 = neg_count(F(1, 2), U(F(1, 2)))
print(f'control: exclusion claimed at lam=1/2 (A-U PSD) -> neg pivots {c05}: ' + ('REJECTED (ok)' if c05 >= 1 else 'ACCEPTED (CONTROL FAILED)'))
out['control_half'] = c05
# Reading 2: ratio lambda_min/U at lam = 1 and lam = 1/2
out['ratio_at_1'] = lmin(1.0) / float(U(F(1))); out['ratio_at_half'] = lmin(0.5) / float(U(F(1, 2)))
# Reading 3: second eigenvalue lambda_2(A) = U
f2 = lambda l: evals(l)[1] - float(U(F(l)))
r3 = [(round(a, 4), round(b, 4)) for a, b in zip(np.linspace(0.01, 5, 500)[:-1], np.linspace(0.01, 5, 500)[1:]) if f2(a) * f2(b) < 0]
out['reading3_lambda2_eq_U_sign_changes'] = r3
# Reading 4: U compared with the per-plaquette normalised lambda_min (lambda_min / P) or U scaled by P
f4 = lambda l: lmin(l) / P - float(U(F(l))) / P
# Reading 5: lambda_min(A) - U where retained matrix uses lam/2 (other normalisation of Re chi)
f5 = lambda l: lmin(l / 2) - float(U(F(l)))
for nm, fn in (('reading5_halfcoupling', f5),):
    sc_ = [(round(a, 4), round(b, 4)) for a, b in zip(np.linspace(0.01, 5, 500)[:-1], np.linspace(0.01, 5, 500)[1:]) if fn(a) * fn(b) < 0]
    out[nm + '_sign_changes'] = sc_
print('ratios lambda_min/U at lam=1, 1/2:', out['ratio_at_1'], out['ratio_at_half'])
print('reading 3 (lambda_2 = U) sign changes:', r3)
print('reading 5 (retained at lam/2) sign changes:', out['reading5_halfcoupling_sign_changes'])
json.dump(out, open(HERE / 'dcube_test_b.json', 'w'), indent=1, default=str)

# All lam above the bracket: A(lam) - U(lam) I = (diag(E) - 28/3) + lam((33 - K) I - S) is affine in lam, so
# f(lam) = lambda_min(A) - U is concave with f'(lam) >= lim f/lam = lambda_min((33-K) I - S). If (33-K) I - S is
# positive definite (exact LDL), f is increasing everywhere, so f(lam_hi) >= 0 gives f >= 0 for every lam >= lam_hi.
B = [[(3 * P - K if i == j else F(0)) - S[i][j] for j in range(n)] for i in range(n)]
nb = sc.interval_inertia(B)[0]
print(f'(33-K) I - S: negative pivots = {nb} (0 => positive definite => exclusion holds for every lam >= the upper bracket end)')
Bc = [[(F(5, 2) if i == j else F(0)) - S[i][j] for j in range(n)] for i in range(n)]   # control: (5/2) I - S is NOT PSD (sigma_max(S) = 2.67)
try: nbc = sc.interval_inertia(Bc)[0]
except ArithmeticError: nbc = 'uncertified pivot (not accepted)'
print(f'control: (5/2) I - S claimed PSD -> negative pivots = {nbc}: ' + ('REJECTED (ok)' if nbc != 0 else 'ACCEPTED (CONTROL FAILED)'))
out['slope_matrix_neg_pivots'] = nb; out['slope_control_neg_pivots'] = nbc
json.dump(out, open(HERE / 'dcube_test_b.json', 'w'), indent=1, default=str)
