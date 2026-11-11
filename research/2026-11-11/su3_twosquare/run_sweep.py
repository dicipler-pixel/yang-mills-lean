"""Cutoff sweep for the SU(3) two-square gap, ink 2026-11-11. Appends rows to results_sweep.csv."""
import os; os.environ["OMP_NUM_THREADS"]="1"; os.environ["OPENBLAS_NUM_THREADS"]="1"
import sys, time, csv, os, numpy as np, theta_gt as tg
LAMS = [0.1, 0.5, 1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128]
ECUTS = [float(x) for x in sys.argv[1:]] or [40/3 + 1e-9, 60, 80, 100, 125, 150, 175, 200]
out = 'results_sweep.csv'; new = not os.path.exists(out)
with open(out, 'a', newline='') as fh:
    w = csv.writer(fh)
    if new: w.writerow(['ECUT', 'states', 'nnz', 'lambda', 'E0', 'E1', 'E2', 'E3', 'gap', 'gap_over_2sqrt3lam', 'build_s'])
    for ec in ECUTS:
        t = time.time(); st, E, S, T = tg.build(ec, lean=True); bt = time.time() - t; del st
        for lam in LAMS:
            L = tg.levels_T(E, T, lam, 4)
            g = L[1] - L[0]
            w.writerow([f'{ec:.6g}', len(E), 2 * T.nnz, lam] + [f'{x:.12f}' for x in L] + [f'{g:.12f}', f'{g/(2*np.sqrt(3*lam)):.10f}', f'{bt:.1f}'])
            fh.flush()
        print('done', ec, len(E), f'{time.time()-t:.0f}s', flush=True)
