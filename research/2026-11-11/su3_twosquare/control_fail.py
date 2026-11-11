"""Must-fail controls for the SU(3) two-square truncated gap, ink 2026-11-11.

Two false claims are tested against a live build of the truncated Hamiltonian
H(λ) = E_el + λ(6 − Re Tr U − Re Tr V) at ECUT=80, λ=8 (already in results_sweep.csv):

  C1. The gap is at least the computed value plus 1/1000.
  C2. Flipping the sign of the recoupling / magnetic matrix (T → −T) leaves the
      gap unchanged (within 1e-8).

Both must be rejected. This is a numerical control on a finite truncated
Hamiltonian, not a continuum or mass-gap claim.
"""
import os
os.environ["OMP_NUM_THREADS"] = "1"
os.environ["OPENBLAS_NUM_THREADS"] = "1"
import sys, time, numpy as np, scipy.sparse.linalg as sla, theta_gt as tg

ECUT = 80
LAM = 8.0
TOL_SAME = 1e-8
CSV_GAP = 7.803490638396  # results_sweep.csv, ECUT=80, λ=8
CSV_E0 = 33.489184069159
CSV_E1 = 41.292674707555

def levels_wrong_sign(E, T, lam, k=4):
    """Same as levels_T but with T → −T, i.e. magnetic term flips sign."""
    D = len(E)
    d = E + 6 * lam
    TT = T.T
    # correct: d*x - 0.5*lam*(T+T^T)x ; wrong sign: d*x + 0.5*lam*(T+T^T)x
    op = sla.LinearOperator(
        (D, D),
        matvec=lambda x: d * x + 0.5 * lam * (T @ x + TT @ x),
        dtype=float,
    )
    w = sla.eigsh(op, k=k, which="SA", tol=1e-12, maxiter=200000)[0]
    return np.sort(w)

t0 = time.time()
st, E, S, T = tg.build(ECUT, lean=True)
L = tg.levels_T(E, T, LAM, 4)
gap = float(L[1] - L[0])
E0, E1 = float(L[0]), float(L[1])
print(f"live build ECUT={ECUT} states={len(E)} λ={LAM}")
print(f"  E0={E0:.12f}  E1={E1:.12f}  E2={L[2]:.12f}  E3={L[3]:.12f}")
print(f"  gap={gap:.12f}")
print(f"  vs CSV |dE0|={abs(E0-CSV_E0):.3e} |dE1|={abs(E1-CSV_E1):.3e} |dgap|={abs(gap-CSV_GAP):.3e}")
assert abs(gap - CSV_GAP) < 1e-9, "live gap does not match results_sweep.csv"
assert abs(E0 - CSV_E0) < 1e-9 and abs(E1 - CSV_E1) < 1e-9

# C1: claim gap >= computed + 1/1000
claimed = gap + 1.0 / 1000.0
c1_holds = gap >= claimed
print()
print("CONTROL C1: claim  gap  ≥  computed_gap + 1/1000")
print(f"  computed_gap           = {gap:.12f}")
print(f"  claimed lower bound    = {claimed:.12f}")
print(f"  computed_gap - claimed = {gap - claimed:.12f}")
print(f"  claim holds? {c1_holds}")
print(f"  RESULT: {'ACCEPTED (UNEXPECTED)' if c1_holds else 'REJECTED'}")
if c1_holds:
    print("CONTROL FAILED TO REJECT C1", file=sys.stderr)
    sys.exit(1)

# C2: wrong recoupling / magnetic sign
Lw = levels_wrong_sign(E, T, LAM, 4)
gap_w = float(Lw[1] - Lw[0])
c2_holds = abs(gap_w - gap) < TOL_SAME
print()
print("CONTROL C2: claim  flipping the recoupling sign (T → −T) leaves the gap unchanged")
print(f"  correct-sign gap = {gap:.12f}")
print(f"  wrong-sign gap   = {gap_w:.12f}")
print(f"  |difference|     = {abs(gap_w-gap):.12f}")
print(f"  wrong-sign E0,E1,E2,E3 = " + ", ".join(f"{x:.12f}" for x in Lw))
print(f"  claim holds? {c2_holds}")
print(f"  RESULT: {'ACCEPTED (UNEXPECTED)' if c2_holds else 'REJECTED'}")
if c2_holds:
    print("CONTROL FAILED TO REJECT C2", file=sys.stderr)
    sys.exit(1)

print()
print(f"both controls rejected in {time.time()-t0:.1f}s")
print("PASS")
