# SU(3) two-square spectral gap (truncated Kogut–Susskind Hamiltonian)

This is a truncated-Hamiltonian numerical study on a two-plaquette lattice, not a continuum or mass-gap claim. It reports the lowest spectral gap of the SU(3) Kogut–Susskind Hamiltonian on two plaquettes that share a link (the theta graph, arms 1, 3, 3), in a Gelfand–Tsetlin recoupling basis. The numbers below are gaps of a **finite truncated Hamiltonian**. No continuum, mass-gap, or Millennium claim is made.

Author: Jeromie Beasley. Licence: MIT for code, CC BY 4.0 for prose — see LICENSING.md. Code and sweep live in this folder, reusing the existing GT / recoupling build (`gt_su3.py`, `theta_gt.py`, `run_sweep.py`). ECUT = 300 was run at \(\lambda=64\) only (`run_ecut300_lam64.py`); other couplings at that cutoff, including \(\lambda=128\), were not run. The driver `run_ecut300_lam128.py` is included but has no results file.

## Method

The Hamiltonian and conventions match the repository 19-state cell and `sn_theta.py`:

\[
H(\lambda) = E_{\mathrm{el}} + \lambda\,(6 - \mathrm{Re}\,\mathrm{Tr}\,U - \mathrm{Re}\,\mathrm{Tr}\,V),\qquad \alpha = 1.
\]

The physical space is the gauge-invariant spin-network space with basis \(|b\,c\,a\,k\,l\rangle\), where \(a\) occurs in \(b\otimes c\) with multiplicity labels \(k,l\). The electric term is

\[
E_{\mathrm{el}} = 3\,c(b) + 3\,c(c) + c(a),\qquad c(p,q)=\frac{p^2+q^2+pq+3p+3q}{3},\quad c(1,0)=\frac{4}{3}.
\]

Multiplication by \(\mathrm{Tr}\,U\) and \(\mathrm{Tr}\,V\) is computed from the SU(3) recoupling (6j) matrix with one fundamental leg, evaluated on highest-weight vectors in the Gelfand–Tsetlin basis (`gt_su3.py`). The truncation is Galerkin: keep states with \(E_{\mathrm{el}}\le\mathrm{ECUT}\). These are nested subspaces, so each truncated level is an upper bound on the corresponding untruncated level and decreases as ECUT grows. The gap \(\Delta = E_1-E_0\) of the truncated operator is **not** itself a bound on the untruncated gap.

The comparison scale is \(2\sqrt{3\lambda}\). Reported ratios are \(\Delta/(2\sqrt{3\lambda})\).

Structural checks already recorded in `check_recoupling.out`:

1. gl(3) relations and Casimir in the GT irreps, max error \(7.11\times 10^{-14}\) on \(p,q\le 8\).
2. Racah–Speiser multiplicities satisfy \(\sum_a N_a d_a = d_b d_c\) (max residual 0 on the tested range).
3. Recoupling orthogonality: 112 blocks \((b,c,a')\), max \(|RR^T-1| = 2.66\times 10^{-15}\).

The 19-state cutoff ECUT \(= 40/3\) reproduces the repository pencil (`test_small.py`): at \(\lambda=1\), \((E_0,E_1)=(5.794809953920,\,10.725853203900)\); at \(\lambda=4\), \((20.408292727939,\,25.823370426708)\). Arm cutoffs \(K=3\) (367 states) and \(K=4\) (1282 states) match `theta_reference.json` / `sn_theta.py` to about \(10^{-13}\) on all twelve reference couplings except exactly \(\lambda=0\). At \(\lambda=0\) the operator is diagonal; its lowest electric values are \(0,16/3,16/3\). For dimension \(>300\) the sparse eigensolver missed the isolated zero at exactly \(\lambda=0\) and returned the \(16/3\) cluster. That does not affect this sweep (smallest \(\lambda\) is 0.1, and those levels match).

The sweep is `run_sweep.py`: for each ECUT the magnetic matrix is built once, then the lowest four eigenvalues of \(H(\lambda)\) are computed for \(\lambda\in\{0.1,0.5,1,2,3,4,6,8,12,16,24,32,48,64,96,128\}\). Raw rows are in `results_sweep.csv`. Logs: `sweep.log`, `sweep250.log`. The ECUT = 300, \(\lambda=64\) run is in `results_ecut300_lam64.csv` and `ecut300_lam64.log`.

## Gap table versus \(\lambda\)

Highest cutoff reached: **ECUT = 250**, 231800 states, 31 476 360 stored matrix entries (symmetric count \(2\times\) nnz of the one-sided recoupling matrix \(T\)), build 725.3 s, build plus all 16 eigenvalue solves 957 s. In the table, \(|\Delta_{\mathrm{gap}}|\) is the absolute change relative to ECUT = 200 (100184 states). Relative digits are \(\lfloor -\log_{10}(|\Delta_{\mathrm{gap}}|/\Delta_{250})\rfloor\) when the change is nonzero, else 12.

| \(\lambda\) | \(E_0\) | \(E_1\) | gap \(\Delta\) | \(\Delta/(2\sqrt{3\lambda})\) | \(\lvert\Delta_{\mathrm{gap}}\rvert\) vs 200 | rel. digits vs 200 |
|---:|---:|---:|---:|---:|---:|---:|
| 0.1 | 0.598107373786 | 5.882177574256 | 5.284070200470 | 4.8236740737 | 0 | 12 |
| 0.5 | 2.950904810281 | 8.054099360238 | 5.103194549957 | 2.0833704509 | 0 | 12 |
| 1 | 5.794723397655 | 10.714742173554 | 4.920018775899 | 1.4202870823 | 0 | 12 |
| 2 | 11.112747233753 | 15.847809405722 | 4.735062171970 | 0.9665405185 | \(1.0\times 10^{-12}\) | 12 |
| 3 | 15.891177631356 | 20.725452127774 | 4.834274496417 | 0.8057124161 | 0 | 12 |
| 4 | 20.143917394545 | 25.349263836105 | 5.205346441560 | 0.7513270423 | 0 | 12 |
| 6 | 27.390845671288 | 33.825363275736 | 6.434517604448 | 0.7583151720 | \(1.0\times 10^{-12}\) | 12 |
| 8 | 33.489179627595 | 41.292599746451 | 7.803420118855 | 0.7964332308 | 0 | 12 |
| 12 | 43.670920370100 | 53.856010152713 | 10.185089782613 | 0.8487574819 | 0 | 12 |
| 16 | 52.226712368928 | 64.367803302195 | 12.141090933267 | 0.8762077648 | \(1.5\times 10^{-10}\) | 10 |
| 24 | 66.550493537516 | 81.903148379969 | 15.352654842452 | 0.9046638624 | \(1.5\times 10^{-7}\) | 8 |
| 32 | 78.610560365195 | 96.637577686229 | 18.027017321033 | 0.9199373754 | \(9.8\times 10^{-6}\) | 6 |
| 48 | 98.824807875793 | 121.306889310689 | 22.482081434896 | 0.9367533931 | \(1.26\times 10^{-3}\) | 4 |
| 64 | 115.856857955890 | 142.079326711965 | 26.222468756074 | 0.9462218372 | \(1.92\times 10^{-2}\) | 3 |
| 96 | 144.419822834295 | 176.922387163990 | 32.502564329694 | 0.9576159851 | \(3.33\times 10^{-1}\) | 1 |
| 128 | 168.514413340492 | 206.462520877072 | 37.948107536580 | 0.9682656268 | \(1.29\) | 1 |

Source: `results_sweep.csv` and `gap_table_ecut250.csv`. On this sweep both \(E_0\) and \(E_1\) are monotonically nonincreasing in ECUT, as expected for a Galerkin truncation.

The ratio \(\Delta/(2\sqrt{3\lambda})\) dips to about 0.75 near \(\lambda=4\) (0.7513 at \(\lambda=4\), from the ECUT = 250 table). A bound of the form gap \(\ge 2\sqrt{3\lambda}\) therefore fails at intermediate coupling even in this truncation.

## Convergence in the representation cutoff

Nine electric cutoffs were completed across the full coupling list: 40/3 (19 states), 60, 80, 100, 125, 150, 175, 200, and 250. A tenth cutoff, ECUT = 300 (465572 states), was run at \(\lambda=64\) only. Gaps at five representative couplings:

| ECUT | states | build (s) | \(\lambda=1\) | \(\lambda=8\) | \(\lambda=32\) | \(\lambda=64\) | \(\lambda=128\) |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 13.3333 | 19 | 0.4 | 4.931043249980 | 8.117927444606 | 26.528213845343 | 51.176316333503 | 100.469746364526 |
| 60 | 1343 | 2.6 | 4.920018775899 | 7.809278495214 | 22.122294855726 | 40.183025509915 | 76.750747019400 |
| 80 | 3648 | 5.0 | 4.920018775898 | 7.803490638396 | 19.583591815575 | 34.657989481329 | 64.920107505040 |
| 100 | 7912 | 8.4 | 4.920018775898 | 7.803420861070 | 18.430517615584 | 30.842955067157 | 56.454169349606 |
| 125 | 17659 | 19.1 | 4.920018775898 | 7.803420121012 | 18.071662517757 | 28.005806510339 | 48.801544802634 |
| 150 | 34375 | 45.9 | 4.920018775899 | 7.803420118861 | 18.030284697612 | 26.742292880765 | 44.009273333835 |
| 175 | 60601 | 91.3 | 4.920018775898 | 7.803420118855 | 18.027211921234 | 26.337028884915 | 41.037977082632 |
| 200 | 100184 | 341.7 | 4.920018775899 | 7.803420118855 | 18.027027157226 | 26.241703525651 | 39.239918487234 |
| 250 | 231800 | 725.3 | 4.920018775899 | 7.803420118855 | 18.027017321033 | 26.222468756074 | 37.948107536580 |
| 300 | 465572 | 1173.6 | — | — | — | 26.222088605059 | — |

**Verdict (digits stable between ECUT 200 and 250):**

- \(\lambda\le 12\): 12 agreeing digits (change at most \(10^{-12}\), at eigensolver precision). Already stable from much smaller cutoffs: e.g. \(\lambda=1\) is settled by ECUT = 60, \(\lambda=8\) by ECUT = 150.
- \(\lambda=16\): 10 digits (\(\lvert\Delta\rvert=1.5\times 10^{-10}\)).
- \(\lambda=24\): 8 digits (\(\lvert\Delta\rvert=1.5\times 10^{-7}\)).
- \(\lambda=32\): 6 digits (\(\lvert\Delta\rvert=9.8\times 10^{-6}\)). The 175→200 step was \(1.8\times 10^{-4}\), so six digits are the honest stable count.
- \(\lambda=48\): 4 digits (\(\lvert\Delta\rvert=1.26\times 10^{-3}\)). Still moving in the fourth digit.
- \(\lambda=64\): settled between ECUT 250 and 300 by the criterion \(\lvert\Delta\mathrm{gap}\rvert<10^{-3}\) and shrinking. The ECUT = 300 gap is 26.222088605059, which is \(3.80\times 10^{-4}\) below the ECUT = 250 value 26.222468756074 (four relative digits) and \(1.96\times 10^{-2}\) below the ECUT = 200 value 26.241703525651. The 250→300 change is about 50 times smaller than the 200→250 step (0.0192). Both \(E_0\) and \(E_1\) continued to decrease.
- \(\lambda=96\) and \(\lambda=128\): not converged. Changes of 0.33 and 1.29 respectively; only the leading digit is usable. These truncated gaps are still falling as ECUT grows.

Consequently the ratio \(\Delta/(2\sqrt{3\lambda})\) is settled through \(\lambda=32\) (and to about four digits at \(\lambda=48\)), and at \(\lambda=64\) the ECUT = 300 ratio 0.9462081197 is settled to about four digits versus ECUT = 250. At \(\lambda=96\) and \(\lambda=128\) the ECUT = 250 ratios (0.958 and 0.968) have not converged, so the large-\(\lambda\) ratio is **not** claimed.

ECUT = 300 was run at \(\lambda=64\) only: 465572 states, 38 787 867 entries in the one-sided recoupling matrix \(T\) (symmetric count 77 575 734), build 1173.6 s, one eigensolve 25.0 s, total 1199.0 s. No \(\lambda=128\) run was done at this cutoff. Source: `results_ecut300_lam64.csv` and `ecut300_lam64.log`.

## Controls that must fail

Both controls were run live against a fresh ECUT = 80 build at \(\lambda=8\) (3648 states). The live gap matched `results_sweep.csv` to \(4\times 10^{-13}\). Script: `control_fail.py`. Log: `control_fail.out`.

**C1.** Claim: the truncated gap is at least the computed value plus \(1/1000\).

- computed gap = 7.803490638396
- claimed lower bound = 7.804490638396
- computed − claimed = −0.001
- **REJECTED**

**C2.** Claim: flipping the recoupling / magnetic sign (\(T\to -T\)) leaves the gap unchanged (within \(10^{-8}\)).

- correct-sign gap = 7.803490638396
- wrong-sign gap = 3.165926369279
- difference = 4.637564269117
- wrong-sign levels: 41.572248506239, 44.738174875518, 44.746180064755, 47.515671293022
- **REJECTED**

Both controls rejected in under 3 s. PASS.

## Open items

- \(\lambda=96\) and \(\lambda=128\) still need a higher electric cutoff before the gap or the ratio to \(2\sqrt{3\lambda}\) can be quoted to several stable digits. \(\lambda=64\) is now settled to about four digits between ECUT 250 and 300.
- The large-\(\lambda\) asymptotic of the *untruncated* two-square gap is therefore still open. This work does not extrapolate it.
- These numbers are not yet a Lean certificate.
- The named hypothesis `CentreCharacter` and the gauge-support regrouping (Layer 2) are separate Lean items; they are not used here.

## Files

| file | role |
|---|---|
| `gt_su3.py` | Gelfand–Tsetlin SU(3) irreps |
| `theta_gt.py` | two-square Hamiltonian in the GT recoupling basis |
| `run_sweep.py` | cutoff sweep driver |
| `results_sweep.csv` | all computed levels, gaps, and ratios |
| `gap_table_ecut250.csv` | ECUT = 250 table with vs-200 digits |
| `sweep.log`, `sweep250.log` | build logs through ECUT 200 and 250 |
| `check_recoupling.py`, `check_recoupling.out` | structural checks |
| `test_small.py`, `test_k4.py` | 19-state, \(K=3\), and \(K=4\) checks |
| `control_fail.py`, `control_fail.out` | must-fail controls |
| `run_ecut300_lam64.py` | single-coupling driver for ECUT = 300, \(\lambda=64\) |
| `results_ecut300_lam64.csv` | ECUT = 300, \(\lambda=64\) levels, gap, and changes vs 250 and 200 |
| `ecut300_lam64.log` | build and eigensolve log for that run |
| `run_ecut300_lam128.py` | single-coupling driver for ECUT = 300, \(\lambda=128\); not run, no results file |
| `one_plaquette.py` | one-plaquette helper, not used in the table |

Jeromie Beasley · licence MIT for code, CC BY 4.0 for prose — see LICENSING.md · ORCID https://orcid.org/0009-0006-4645-5643 · GitHub dicipler-pixel · X @d1c1pler · YouTube @AtlasMemoriae (https://www.youtube.com/@AtlasMemoriae) · website https://atlas-memoriae.dicipler.workers.dev
