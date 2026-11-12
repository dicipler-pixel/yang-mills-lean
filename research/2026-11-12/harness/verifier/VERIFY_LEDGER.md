# VERIFY LEDGER (verifier agent)

Working copy: `/home/claude/ym-harness/work/verifier` (yang-mills-lean at ff9c203). Outputs: `/home/claude/ym-harness/out/verifier`. Every row below is an observed run, with its real exit code. Wall time is seconds, measured by the harness. Output tails follow the table.

| # | Path | Exact command | Exit | Wall (s) | Status | Key counts printed |
|---|---|---|---:|---:|---|---|
| 1 | `paper/2026-09-08/su3/su3_character_certificate.py` | `cd paper/2026-09-08 && python3 -S su3/su3_character_certificate.py` | 0 | 2 | PASS | 13587 exact assertions; 20 exact inertia certificates; 2275 pivot signs |
| 2 | `paper/2026-09-08/run_all.py` | `cd paper/2026-09-08 && python3 run_all.py (first attempt exit 1: sympy missing; installed sympy 1.14.0 with pip --break-system-packages; rerun below)` | 0 | 6 | PASS | su3: 13587 / 20 / 2275; frame: 67 exact rational controls, status passed; holonomy: 24 assertions passed; instanton charge -1 |
| 3 | `research/yang_mills_2026_09_09/cross_theorem/native/recheck.py` | `cd research/yang_mills_2026_09_09/cross_theorem/native && python3 -S recheck.py --out <work>/.../native/fresh_evidence_verifier` | 0 | 328 | PASS | 58 accepted primary targets (two 14, strip 14, corner 14, cube 10, double_cube 6); 90 native outputs; all four false-premise controls recorded as status blocked (SUMMARY.json) |
| 4 | `research/yang_mills_2026_09_09/scripts/two_plaquette_certificate.py` | `python3 two_plaquette_certificate.py --out <out>/p2_scripts/two_plaquette_results.json` | 0 | 1 | PASS | exact checks 609; deliberately rejected controls 3; 6 certificates; lambda/alpha=1 gap >= 2.847077 (7-state bare) |
| 5 | `research/yang_mills_2026_09_09/scripts/two_plaquette_19.py` | `python3 two_plaquette_19.py --out <out>/p2_scripts/two_plaquette_19_results.json` | 0 | 3 | PASS | exact checks 694; refusals 2; 24 inertia certificates; 2448 pivot signs; lambda=1 gap >= 4.908928 |
| 6 | `research/yang_mills_2026_09_09/scripts/two_plaquette_extended.py` | `python3 two_plaquette_extended.py --out <out>/p2_scripts/two_plaquette_extended_results.json` | 0 | 2 | PASS | exact checks 562; refusals 2; 20 inertia certificates; 1980 pivot signs; lambda=1 gap >= 4.883646 |
| 7 | `research/yang_mills_2026_09_09/scripts/lifted_two_plaquette_certificate.py` | `python3 lifted_two_plaquette_certificate.py --out <out>/p2_scripts/lifted_two_plaquette_results.json` | 0 | 2 | PASS | Haar/structure checks 609; base refusals 3; extra refusals 6; 32 inertia certificates; 2016 pivot signs |
| 8 | `research/yang_mills_2026_09_09/scripts/local_window_budget.py` | `python3 local_window_budget.py --out <out>/p2_scripts/local_window_budgets.json` | 0 | 0 | PASS | 15 budget rows (L in 3,10,100 x lambda in 0,1/10,1,10,100); 316 exact controls; 6 invalid inputs rejected |
| 9 | `research/window_wall_2026_11_10/window_wall_01.py` | `cd research/window_wall_2026_11_10 && python3 window_wall_01.py <work> <out>/window_wall_01.json` | 0 | 165 | PASS | output identical to shipped window_wall_01.out (0 differing lines, timing excluded) |
| 10 | `research/window_wall_2026_11_10/window_wall_certified_02.py` | `cd research/window_wall_2026_11_10 && python3 window_wall_certified_02.py <work> <out>/window_wall_certified_02.json` | 0 | 74 | PASS | 80 one-loop certificates, N=30, h=1/1000; stored targets inside excluded cells = 0; identical to shipped .out |
| 11 | `research/window_wall_2026_11_10/certify_58_windows.py` | `cd research/window_wall_2026_11_10 && python3 certify_58_windows.py 20` | 0 | 6 | PASS | 58 targets checked, 0 violations; smallest slack 0.000275882; identical to shipped N20 .out |
| 12 | `research/window_wall_2026_11_10/certify_slopes.py` | `cd research/window_wall_2026_11_10 && python3 certify_slopes.py 20` | 0 | 5 | PASS | table of EXCLUDED / not excluded cells (strip and corner not excluded at lambda=4; cube, double_cube, two excluded); writes certify_slopes_N20.json (no shipped copy to compare) |
| 13 | `research/window_wall_2026_11_10/cells/window_wall_endpoints_03.py` | `cd research/window_wall_2026_11_10/cells && python3 window_wall_endpoints_03.py <work> <out>/window_wall_endpoints_03.json` | 0 | 13 | PASS | margins sum c*L - 28/3: two 1.4512, strip 0.1241, corner 0.4204, cube 2.0306, double_cube 2.5889; JSON identical to shipped |
| 14 | `research/window_wall_2026_11_10/dcube_uniform/certify_dcube_uniform.py` | `cd research/window_wall_2026_11_10/dcube_uniform && python3 certify_dcube_uniform.py` | 0 | 1 | PASS | U = -4435334032736196355095411672194503/227640311408488358377099027485000000000 (~ -1.9484e-5); EXCLUDED (certified); identical to shipped .out |
| 15 | `research/window_wall_2026_11_10/string_floor/strip_string.py` | `cd research/window_wall_2026_11_10/string_floor && python3 strip_string.py` | 0 | 0 | PASS | strip 28 pairs / corner 21 / cube 28: 0 mismatches each; identical to shipped .out |
| 16 | `research/window_wall_2026_11_10/varying_s/exact_t.py` | `cd research/window_wall_2026_11_10/varying_s && python3 exact_t.py` | 0 | 10 | PASS | t: two 4/3, cube 7/9, strip 32/35..36/35 before vertex rule; identical to shipped .out |
| 17 | `research/window_wall_2026_11_10/varying_s/strip_settle.py` | `cd research/window_wall_2026_11_10/varying_s && python3 strip_settle.py` | 0 | 1 | PASS | strip exact upper t = 1; corner t = 10/9; identical to shipped .out |
| 18 | `research/window_wall_2026_11_10/varying_s/strip_lower.py` | `cd research/window_wall_2026_11_10/varying_s && python3 strip_lower.py` | 0 | 0 | PASS | exact lower t = 1 for strip; identical to shipped .out |
| 19 | `research/window_wall_2026_11_10/varying_s/varying_s_lp.py` | `cd research/window_wall_2026_11_10/varying_s && python3 varying_s_lp.py` | 0 | 6 | PASS | strip excluded=False (t*<=1.02857, the pre-vertex-rule 36/35); corner False; cube True (t*<=7/9); double_cube True (t*<=0.46667 = 7/15); identical to shipped .out |
| 20 | `research/window_wall_2026_11_10/varying_s/lambda_scan.py` | `cd research/window_wall_2026_11_10/varying_s && python3 lambda_scan.py` | 0 | 8 | PASS | strip and corner excluded at each scanned lambda from 6 up; identical to shipped .out |
| 21 | `research/2026-11-10/window_wall_endpoints/certify_slopes.py (as shipped, N=28)` | `cd research/2026-11-10/window_wall_endpoints && python3 certify_slopes.py 28` | 1 | 0 | FAIL | ModuleNotFoundError: su3_character_certificate. Hardcoded YM path /workspace/yang-mills-lean/research/yang_mills_2026_09_09 (line 10) does not exist on this machine; no outputs written |
| 22 | `research/2026-11-10/window_wall_endpoints/certify_slopes.py (as shipped, N=20)` | `cd research/2026-11-10/window_wall_endpoints && python3 certify_slopes.py 20` | 1 | 0 | FAIL | same hardcoded-path ModuleNotFoundError as N=28; no outputs written |
| 23 | `research/2026-11-10/window_wall_endpoints/certify_slopes.py (supplementary: scratch copy, path line replaced with <work> path; N=28)` | `cd <scratch> && python3 certify_slopes_subst.py 28` | 0 | 16 | PASS | supplementary, not the as-shipped file; output identical to shipped certify_slopes_N28.out |
| 24 | `research/2026-11-10/window_wall_endpoints/certify_slopes.py (supplementary: scratch copy, path substituted; N=20)` | `cd <scratch> && python3 certify_slopes_subst.py 20` | 0 | 5 | PASS | supplementary, not the as-shipped file; no shipped N=20 .out to diff (only certify_slopes_N20.json) |
| 25 | `research/2026-11-10/window_wall_endpoints/lean_green_crosscheck/cert.py 14` | `cd research/2026-11-10/window_wall_endpoints/lean_green_crosscheck && python3 cert.py 14` | 0 | 4 | PASS | strip W'(0) <= -0.108423 EXCLUDED; corner W'(0) <= -0.403503 EXCLUDED |
| 26 | `research/2026-11-10/window_wall_endpoints/lean_green_crosscheck/cert.py 18` | `cd research/2026-11-10/window_wall_endpoints/lean_green_crosscheck && python3 cert.py 18` | 0 | 26 | PASS | strip W'(0) <= -0.108423 EXCLUDED; corner W'(0) <= -0.403503 EXCLUDED |
| 27 | `research/2026-11-10/window_wall_endpoints/lean_green_crosscheck/controls.py` | `cd research/2026-11-10/window_wall_endpoints/lean_green_crosscheck && python3 controls.py` | 0 | 3 | PASS | three mu rows; false z=E+1e-3 certified? False in all three |
| 28 | `research/2026-11-11/kyfan_chord/kyfan_plaquette.py` | `cd research/2026-11-11/kyfan_chord && python3 kyfan_plaquette.py` | 0 | 261 | PASS | K=6 and K=12 uniform min gap 3.668065 on [1/2,2]; identical to shipped .out (timing excluded) |
| 29 | `research/2026-11-11/kyfan_chord/check_19.py` | `cd research/2026-11-11/kyfan_chord && python3 check_19.py` | 0 | 1 | PASS | max \|diff\| over 19 levels <= 3.6e-14 at lambda=0,0.1,1,4; E0,E1 at lambda=1 = 5.79480995, 10.7258532; identical to shipped .out |
| 30 | `research/2026-11-11/kyfan_chord/theta_reference.py` | `not run` |  |  | NOT RUN | README says about 15 minutes (K=4); skipped per instruction. Existing theta_reference.json used by kyfan_theta.py |
| 31 | `research/2026-11-11/kyfan_chord/kyfan_theta.py` | `cd research/2026-11-11/kyfan_chord && python3 kyfan_theta.py` | 0 | 74 | PASS | 1/4-node cover certified gaps: lambda 0.10 5.279411; 0.25 5.213054; 0.50 5.102792; 1.00 4.908798; 1.50 4.698132; 2.00 4.259772; 3.00 2.219518; 4.00 fails (-0.612827); identical to shipped apart from one timing line |
| 32 | `research/2026-11-11/kyfan_certificate_grey/kyfan_cert.py` | `cd research/2026-11-11/kyfan_certificate_grey && python3 kyfan_cert.py` | 0 | 24 | PASS | all 9 controls rejected; uniform gap >= 366806537/100000000 on [1/2,2]; prints 26 rational trial vectors (README says 25); identical to shipped apart from trailing exit line |
| 33 | `research/2026-11-11/kyfan_certificate_grey/b189_five_eighths.py` | `cd research/2026-11-11/kyfan_certificate_grey && python3 b189_five_eighths.py` | 0 | 117 | PASS | c = (mu/24)(<.>_1 - <.>_0) = 5/8 derived (SymPy); doubled-quartic control c=5/4 rejected |
| 34 | `research/2026-11-11/ring_flux_cert/run_cert.py (L=2, cap 18)` | `cd research/2026-11-11/ring_flux_cert && python3 run_cert.py 2 18 18` | 0 | 291 | PASS | lambda 1/4, 1/2, 1: gap_lo 5.209035 / 5.092867 / 4.887084; floor_lo-up at lambda=1 2.627354-2.627608; matches README table and runs/L2_18.log |
| 35 | `research/2026-11-11/ring_flux_cert/run_cert.py (L=3, cap 18)` | `cd research/2026-11-11/ring_flux_cert && python3 run_cert.py 3 18 18` | 0 | 115 | PASS | lambda 1/4, 1/2, 1: gap_lo 5.212463 / 5.100544 / 4.901929; identical SUMMARY lines to shipped ring_L3.out |
| 36 | `research/2026-11-11/ring_flux_cert/float_check.py 2 18` | `cd research/2026-11-11/ring_flux_cert && python3 float_check.py 2 18 (reference float only; a no-argument attempt exited 1 with IndexError)` | 0 | 267 | PASS | float reference only, not a certificate; sector 1 lambda=1 E0 8.422248 E1 8.478464 |
| 37 | `research/2026-11-11/ring_flux_cert/float_check.py 3 18` | `cd research/2026-11-11/ring_flux_cert && python3 float_check.py 3 18 (reference float only)` | 0 | 32 | PASS | float reference only, not a certificate; sector 1 lambda=1 E0 12.668900 E1 12.681264 |
| 38 | `research/2026-11-11/su3_twosquare/test_small.py` | `cd research/2026-11-11/su3_twosquare && python3 test_small.py` | 0 | 1 | PASS | 19-state ECUT=40/3: lambda=1 (5.79480995, 10.7258532); lambda=4 (20.40829273, 25.82337043); matches README |
| 39 | `research/2026-11-11/su3_twosquare/check_recoupling.py` | `cd research/2026-11-11/su3_twosquare && python3 check_recoupling.py` | 0 | 1 | PASS | GT max error 7.1e-14; Racah-Speiser residual 0; 112 blocks, orthogonality 2.66e-15; identical to shipped .out |
| 40 | `research/2026-11-11/su3_twosquare/run_sweep.py` | `not run` |  |  | NOT RUN | skipped per instruction (ECUT 200/250 sweep; the README reports a 725 s build for ECUT 250 alone and a 957 s build plus solves) |
| 41 | `research/2026-11-11/su3_twosquare/run_ecut300_lam64.py` | `not run` |  |  | NOT RUN | skipped per instruction (ECUT 300 run) |
| 42 | `research/2026-11-11/su3_twosquare/run_ecut300_lam128.py` | `not run` |  |  | NOT RUN | skipped per instruction (ECUT 300 run) |
| 43 | `research/spectrum_strip_corner_2026_11_11/dump_dcube.py` | `cd research/spectrum_strip_corner_2026_11_11 && python3 dump_dcube.py` | 0 | 215 | PASS | dimension 95, faces 11, edges 20; rewrote dcube_S.json cache (script reports 212 s; README says about 9 min) |
| 44 | `research/spectrum_strip_corner_2026_11_11/dcube_test_b.py` | `cd research/spectrum_strip_corner_2026_11_11 && python3 dcube_test_b.py` | 0 | 2 | PASS | float crossing lambda* = 0.986695893; exact LDL negative pivots of A-U: 1 at 0.986695, 0 at 0.986697; controls rejected; identical to shipped .out |
| 45 | `research/spectrum_strip_corner_2026_11_11/strip_corner_crossing.py` | `cd research/spectrum_strip_corner_2026_11_11 && python3 strip_corner_crossing.py` | 0 | 15 | PASS | strip excluded from lambda 5.213413 (L_lo 1.00000016 > 1); corner excluded from 5.104165 (L_lo 1.11111121 > 10/9); controls rejected; identical to shipped .out |
| 46 | `scripts/verify.py (full mode)` | `python3 scripts/verify.py (needs lake build / lake env lean)` |  |  | NOT RUN | needs Lean build, not run. No lake or lean binary on this machine; Lean/Mathlib not installed per instruction |
| 47 | `scripts/verify.py --gate-only` | `python3 scripts/verify.py --gate-only (documented no-Lean mode: checks 5 and 6)` | 0 | 1 | PASS | OK (gate only): no banned tokens; 1201 frozen statements match |

Status key: PASS = exit 0 with the printed counts observed. FAIL = non-zero exit, reason in the counts column. NOT RUN = skipped on purpose, reason given. No TIMEOUT occurred.

## Output tails (last 15 lines per script)

### 1. `paper/2026-09-08/su3/su3_character_certificate.py`

```text
Exact structural/arithmetic assertions: 13587
{"lambda_over_kappa": "1/10", "N": 3, "dimension": 10, "scalar_gap_lower_display": 1.2852796307375356, "full_single_loop_gap_lower_display": 1.2868372}
{"lambda_over_kappa": "1", "N": 6, "dimension": 28, "scalar_gap_lower_display": 1.2758093819052136, "full_single_loop_gap_lower_display": 1.3401688}
{"lambda_over_kappa": "10", "N": 10, "dimension": 66, "scalar_gap_lower_display": 2.081403800634878, "full_single_loop_gap_lower_display": 5.6481431}
{"lambda_over_kappa": "100", "N": 25, "dimension": 351, "scalar_gap_lower_display": -33.3376126530834, "full_single_loop_gap_lower_display": 19.36077}
Completed 20 exact inertia certificates; 2275 pivot signs; 1.871 seconds
```

### 2. `paper/2026-09-08/run_all.py`

```text
    "anti_self_dual_12_34",
    "anti_self_dual_13_24",
    "anti_self_dual_14_23",
    "pontryagin_density",
    "charge_integral"
  ],
  "Sodd_cubic_derivative": "-5120/81",
  "Tr_F_wedge_F_density": "48*rho**4/(rho**2 + x1**2 + x2**2 + x3**2 + x4**2)**4",
  "integral_Tr_F_wedge_F": "8*pi**2",
  "charge_convention": "nu = -integral Tr(F wedge F)/(8 pi^2)",
  "charge": -1,
  "scope": "No continuum quantum construction, mass-gap proof, or fresh Lean certificate."
}

All continuation verifiers passed. See the paper for the precise proof scope.
```

### 3. `research/yang_mills_2026_09_09/cross_theorem/native/recheck.py`

```text
two PASS 14 targets
strip PASS 14 targets
corner PASS 14 targets
cube PASS 10 targets
double_cube PASS 6 targets
PASS 58 primary targets, 90 native outputs; no post-exit process
```

### 4. `research/yang_mills_2026_09_09/scripts/two_plaquette_certificate.py`

```text
    "16/3",
    "8",
    "8"
  ],
  "exact_checks": 609,
  "deliberately_rejected_controls": 3,
  "elapsed_seconds": 0.1470225630000641
}
lambda/alpha 1/10 gap >= 660249/125000
lambda/alpha 1/2 gap >= 4891209/1000000
lambda/alpha 1 gap >= 2847077/1000000
lambda/alpha 6/5 gap >= 112973/62500
lambda/alpha 7/5 gap >= 27463/31250
lambda/alpha 3/2 gap >= 104049/250000
Output: /home/claude/ym-harness/out/verifier/p2_scripts/two_plaquette_results.json
```

### 5. `research/yang_mills_2026_09_09/scripts/two_plaquette_19.py`

```text
Exact checks 694 refusals 2 seconds 2.8395553010000185
1/10 gap >= 1056811/200000 = 5.284055
1/2 gap >= 1275697/250000 = 5.102788
1 gap >= 76702/15625 = 4.908928
2 gap >= 2136849/500000 = 4.273698
3 gap >= 1233389/500000 = 2.466778
4 gap >= 991383/1000000 = 0.991383
Output /home/claude/ym-harness/out/verifier/p2_scripts/two_plaquette_19_results.json
```

### 6. `research/yang_mills_2026_09_09/scripts/two_plaquette_extended.py`

```text
Exact checks 562 refusals 2 seconds 2.184782243000086
1/10 gap >= 82563/15625 = 5.284032
1/2 gap >= 1020083/200000 = 5.100415
1 gap >= 2441823/500000 = 4.883646
2 gap >= 998641/250000 = 3.994564
3 gap >= 2121927/1000000 = 2.121927
Output /home/claude/ym-harness/out/verifier/p2_scripts/two_plaquette_extended_results.json
```

### 7. `research/yang_mills_2026_09_09/scripts/lifted_two_plaquette_certificate.py`

```text
Haar/structure checks: 609 ; base refusals: 3 ; extra refusals: 6
lambda/alpha 1/10 d 1765331/187500 gap >= 2641053/500000 = 5.282106
lambda/alpha 1/2 d 16146311/1500000 gap >= 2511913/500000 = 5.023826
lambda/alpha 1 d 18292631/1500000 gap >= 274253/62500 = 4.388048
lambda/alpha 6/5 d 3192249/250000 gap >= 4016471/1000000 = 4.016471
lambda/alpha 7/5 d 5003203/375000 gap >= 1803771/500000 = 3.607542
lambda/alpha 3/2 d 20438951/1500000 gap >= 3396687/1000000 = 3.396687
lambda/alpha 2 d 4517183/300000 gap >= 2417629/1000000 = 2.417629
lambda/alpha 3 d 537683/30000 gap >= 56353/200000 = 0.281765
Accepted: 32 inertia certificates; 2016 strict pivot signs; elapsed 1.8274254739999378
Output: /home/claude/ym-harness/out/verifier/p2_scripts/lifted_two_plaquette_results.json
```

### 8. `research/yang_mills_2026_09_09/scripts/local_window_budget.py`

```text
L 10 links 3000 lambda 0 N 0 error <= 0.0 one-link dimension 1
L 100 links 3000000 lambda 0 N 0 error <= 0.0 one-link dimension 1
L 3 links 81 lambda 1/10 N 4 error <= 0.015857828145777717 one-link dimension 3136
L 10 links 3000 lambda 1/10 N 5 error <= 0.003949271075483466 one-link dimension 9996
L 100 links 3000000 lambda 1/10 N 6 error <= 0.014326348339105415 one-link dimension 27468
L 3 links 81 lambda 1 N 12 error <= 0.03603308648170843 one-link dimension 2012920
L 10 links 3000 lambda 1 N 13 error <= 0.050898269931530724 one-link dimension 3436720
L 100 links 3000000 lambda 1 N 15 error <= 0.029132745261818898 one-link dimension 9093096
L 3 links 81 lambda 10 N 36 error <= 0.05921385597769238 one-link dimension 5020308592
L 10 links 3000 lambda 10 N 38 error <= 0.024141768268431986 one-link dimension 7529232620
L 100 links 3000000 lambda 10 N 41 error <= 0.010072684251496102 one-link dimension 13338499251
L 3 links 81 lambda 100 N 107 error <= 0.057728314292100506 one-link dimension 21525695745345
L 10 links 3000 lambda 100 N 110 error <= 0.023729075844843236 one-link dimension 26721994594736
L 100 links 3000000 lambda 100 N 114 error <= 0.026648834117892435 one-link dimension 35339589450243
Output /home/claude/ym-harness/out/verifier/p2_scripts/local_window_budgets.json
```

### 9. `research/window_wall_2026_11_10/window_wall_01.py`

```text
double_cube     11      4    29.5639  -20.2306  -
double_cube     11      5    36.7557  -27.4224  -
double_cube     11     10    64.6259  -55.2925  -
KILL (b): stored targets sitting where the slope is <= 0 = 0

Periodic cubic lattice (every link in 4 faces, c_p = 1): largest face count P with P*<C2>(lam) < 28/3
lam/alpha       <C2>      P_max    largest side L with 3L^3 <= P_max
     1/20   0.000973     9593.3                                   14
     1/10   0.004034     2313.5                                    9
      1/5   0.017270      540.4                                    5
      1/2   0.125473       74.4                                    2
        1   0.507383       18.4                                    1
        2   1.339302        7.0                                    1
        4   2.538254        3.7                                    1
check of the small-coupling law at lam=1/20: <C2>/lam^2 = 0.38915890716850393  (3/8 = 0.375)
```

### 10. `research/window_wall_2026_11_10/window_wall_certified_02.py`

```text
cube             4                      16.066272    -6.732939  EXCLUDED  -
cube             5                      20.197403   -10.864069  EXCLUDED  -
cube             6                      23.907463   -14.574130  EXCLUDED  -
cube             8                      30.451982   -21.118649  EXCLUDED  -
cube            10                      36.188763   -26.855430  EXCLUDED  -
double_cube      1                       3.111571     6.221762  not excl.  -
double_cube      2                      11.922216    -2.588883  EXCLUDED  -
double_cube      3                      21.345159   -12.011825  EXCLUDED  -
double_cube      4                      29.554018   -20.220685  EXCLUDED  -
double_cube      5                      36.744886   -27.411552  EXCLUDED  -
double_cube      6                      43.204922   -33.871589  EXCLUDED  -
double_cube      8                      54.608825   -45.275492  EXCLUDED  -
double_cube     10                      64.611339   -55.278006  EXCLUDED  -
KILL: stored targets inside a certified-excluded cell = 0
one-loop certificates used: 80  cutoff N = 30  h = 1/1000  grid 2^-192
```

### 11. `research/window_wall_2026_11_10/certify_58_windows.py`

```text
controls rejected: wrong upper and wrong lower endpoint at mu=5/2
targets checked: 58, violations: 0
smallest certified slack: 0.000275882 at two lam=1/10 s=1
```

### 12. `research/window_wall_2026_11_10/certify_slopes.py`

```text
controls rejected: wrong upper and wrong lower endpoint at mu=5/2
strip        lam=  5  sum c g' >= 9.454340   W'(0) <= -0.121007   EXCLUDED (certified)
corner       lam=  5  sum c g' >= 9.750832   W'(0) <= -0.417499   EXCLUDED (certified)
cube         lam=  3  sum c g' >= 11.361133   W'(0) <= -2.027800   EXCLUDED (certified)
double_cube  lam=  2  sum c g' >= 11.919321   W'(0) <= -2.585988   EXCLUDED (certified)
two          lam= 10  sum c g' >= 13.346173   W'(0) <= -4.012840   EXCLUDED (certified)
strip        lam= 10  sum c g' >= 19.895277   W'(0) <= -10.561944   EXCLUDED (certified)
corner       lam= 10  sum c g' >= 19.647312   W'(0) <= -10.313978   EXCLUDED (certified)
cube         lam=  4  sum c g' >= 16.062844   W'(0) <= -6.729510   EXCLUDED (certified)
strip        lam=  4  sum c g' >= 6.857070   W'(0) <= +2.476263   not excluded
corner       lam=  4  sum c g' >= 7.236143   W'(0) <= +2.097190   not excluded
```

### 13. `research/window_wall_2026_11_10/cells/window_wall_endpoints_03.py`

```text
two 8 2 faces  sum c*L = 10.784504815  >= 28/3 by 1.4511714816666668
strip 5 3 faces  sum c*L = 9.457402251  >= 28/3 by 0.12406891766666667
corner 5 3 faces  sum c*L = 9.75377889  >= 28/3 by 0.42044555666666666
cube 3 6 faces  sum c*L = 11.363950416  >= 28/3 by 2.0306170826666667
double_cube 2 11 faces  sum c*L = 11.922216147555556  >= 28/3 by 2.5888828142222224
```

### 14. `research/window_wall_2026_11_10/dcube_uniform/certify_dcube_uniform.py`

```text
controls rejected: wrong upper and wrong lower endpoint at mu=5/2
c = 20/11 x 11  lam = 17347717/10000000 = 1.7347717  h = 1/100000
mu(c)      = 190824887/200000000
mu(c+h)    = 190824887/200001100
E_up(c)    = 194783999171585209525318637/80270952531863700000000000
E_lo(c+h)  = 41289054449689406061947657/17015393805234300000000000
g_up(c)    = 194783999171585209525318637/44149023892525035000000000
g_lo(c+h)  = 82578563078977758707361995424227/18716933185757730000000000000000
secant lo  = 2124647341813257414382612685271672194503/4552806228169767167541980549700000000000
sum c L    = 2124647341813257414382612685271672194503/227640311408488358377099027485000000000
W'(0) <= U = -4435334032736196355095411672194503/227640311408488358377099027485000000000  = -1.9483956973e-05
EXCLUDED (certified)
monotonicity: WindowWallMono carries this exclusion to every larger lambda
```

### 15. `research/window_wall_2026_11_10/string_floor/strip_string.py`

```text
strip pairs 28 mismatches 0
corner pairs 21 mismatches 0
cube pairs 28 mismatches 0
```

### 16. `research/window_wall_2026_11_10/varying_s/exact_t.py`

```text
   lam=5 mu=lam/c=1.5000 L=0.946761 excluded(L>t_upper)=False
   lam=5.25 mu=lam/c=1.5750 L=1.009035 excluded(L>t_upper)=False
   lam=5.5 mu=lam/c=1.6500 L=1.070041 excluded(L>t_upper)=True
   lam=5.75 mu=lam/c=1.7250 L=1.129785 excluded(L>t_upper)=True
   lam=6 mu=lam/c=1.8000 L=1.188293 excluded(L>t_upper)=True
corner: states=49 t_upper=10/9 (1.111111) t_lower=10/9 (1.111111)
   lam=5 mu=lam/c=1.6667 L=1.083426 excluded(L>t_upper)=False
   lam=5.25 mu=lam/c=1.7500 L=1.149423 excluded(L>t_upper)=True
   lam=5.5 mu=lam/c=1.8333 L=1.213909 excluded(L>t_upper)=True
   lam=5.75 mu=lam/c=1.9167 L=1.276936 excluded(L>t_upper)=True
   lam=6 mu=lam/c=2.0000 L=1.338570 excluded(L>t_upper)=True
two: states=10 t_upper=4/3 (1.333333) t_lower=4/3 (1.333333)
   lam=8 mu=lam/c=2.2857 L=1.540225 excluded(L>t_upper)=True
cube: states=516 t_upper=7/9 (0.777778) t_lower=7/9 (0.777778)
   lam=3 mu=lam/c=1.5000 L=0.946761 excluded(L>t_upper)=True
```

### 17. `research/window_wall_2026_11_10/varying_s/strip_settle.py`

```text
strip states 12 exact upper t = 1 1.0
  mixture: [([0, 1, 2, 3, 5, 7, 8], '1/4'), ([2, 3, 4, 5, 6, 8, 9], '1/4'), ([0, 1, 2, 4, 6, 7, 8, 9], '1/4'), ([0, 1, 3, 4, 5, 6, 7, 9], '1/4')]
corner states 13 exact upper t = 10/9 1.1111111111111112
  mixture: [([0, 1, 2, 3, 4, 5, 7], '1/6'), ([0, 1, 2, 3, 5, 6, 8], '1/6'), ([0, 1, 2, 4, 6, 7, 8], '1/6'), ([0, 1, 3, 4, 5, 6, 7, 8], '1/6'), ([0, 2, 3, 4, 5, 6, 7, 8], '1/6'), ([1, 2, 3, 4, 5, 6, 7, 8], '1/6')]
```

### 18. `research/window_wall_2026_11_10/varying_s/strip_lower.py`

```text
edges [(0, 1), (0, 4), (1, 2), (1, 5), (2, 3), (2, 6), (3, 7), (4, 5), (5, 6), (6, 7)]
s ['1/4', '0', '1/4', '1/12', '1/4', '1/6', '0', '0', '0', '0']
exact lower t 1 1.0
```

### 19. `research/window_wall_2026_11_10/varying_s/varying_s_lp.py`

```text
two: E=7 trial states=4 t*<=1.33333 (uniform 28/3/E=1.33333) L=1.54023 margin L-t=0.20689 excluded=True
strip: E=10 trial states=10 t*<=1.02857 (uniform 28/3/E=0.93333) L=0.94676 margin L-t=-0.08181 excluded=False
corner: E=9 trial states=13 t*<=1.11111 (uniform 28/3/E=1.03704) L=1.08343 margin L-t=-0.02769 excluded=False
cube: E=12 trial states=96 t*<=0.77778 (uniform 28/3/E=0.77778) L=0.94676 margin L-t=0.16898 excluded=True
double_cube: E=20 trial states=1449 t*<=0.46667 (uniform 28/3/E=0.46667) L=0.59652 margin L-t=0.12986 excluded=True
```

### 20. `research/window_wall_2026_11_10/varying_s/lambda_scan.py`

```text
strip 6 1.18829 excluded
strip 7 1.41079 excluded
strip 8 1.61711 excluded
strip 10 1.99193 excluded
strip 12 2.3288 excluded
corner 6 1.33857 excluded
corner 7 1.5725 excluded
corner 8 1.78922 excluded
corner 10 2.18303 excluded
```

### 21. `research/2026-11-10/window_wall_endpoints/certify_slopes.py (as shipped, N=28)`

```text
Traceback (most recent call last):
  File "/home/claude/ym-harness/work/verifier/research/2026-11-10/window_wall_endpoints/certify_slopes.py", line 13, in <module>
    import su3_character_certificate as su
ModuleNotFoundError: No module named 'su3_character_certificate'
```

### 22. `research/2026-11-10/window_wall_endpoints/certify_slopes.py (as shipped, N=20)`

```text
Traceback (most recent call last):
  File "/home/claude/ym-harness/work/verifier/research/2026-11-10/window_wall_endpoints/certify_slopes.py", line 13, in <module>
    import su3_character_certificate as su
ModuleNotFoundError: No module named 'su3_character_certificate'
```

### 23. `research/2026-11-10/window_wall_endpoints/certify_slopes.py (supplementary: scratch copy, path line replaced with <work> path; N=28)`

```text
controls rejected: wrong upper and wrong lower endpoint at mu=5/2
strip        lam=  5  sum c g' >= 9.454340   W'(0) <= -0.121007   EXCLUDED (certified)
corner       lam=  5  sum c g' >= 9.750832   W'(0) <= -0.417499   EXCLUDED (certified)
cube         lam=  3  sum c g' >= 11.361133   W'(0) <= -2.027800   EXCLUDED (certified)
double_cube  lam=  2  sum c g' >= 11.919321   W'(0) <= -2.585988   EXCLUDED (certified)
two          lam= 10  sum c g' >= 13.346173   W'(0) <= -4.012840   EXCLUDED (certified)
strip        lam= 10  sum c g' >= 19.895277   W'(0) <= -10.561944   EXCLUDED (certified)
corner       lam= 10  sum c g' >= 19.647312   W'(0) <= -10.313978   EXCLUDED (certified)
cube         lam=  4  sum c g' >= 16.062844   W'(0) <= -6.729510   EXCLUDED (certified)
strip        lam=  4  sum c g' >= 6.857070   W'(0) <= +2.476263   not excluded
corner       lam=  4  sum c g' >= 7.236143   W'(0) <= +2.097190   not excluded
```

### 24. `research/2026-11-10/window_wall_endpoints/certify_slopes.py (supplementary: scratch copy, path substituted; N=20)`

```text
controls rejected: wrong upper and wrong lower endpoint at mu=5/2
strip        lam=  5  sum c g' >= 9.454340   W'(0) <= -0.121007   EXCLUDED (certified)
corner       lam=  5  sum c g' >= 9.750832   W'(0) <= -0.417499   EXCLUDED (certified)
cube         lam=  3  sum c g' >= 11.361133   W'(0) <= -2.027800   EXCLUDED (certified)
double_cube  lam=  2  sum c g' >= 11.919321   W'(0) <= -2.585988   EXCLUDED (certified)
two          lam= 10  sum c g' >= 13.346173   W'(0) <= -4.012840   EXCLUDED (certified)
strip        lam= 10  sum c g' >= 19.895277   W'(0) <= -10.561944   EXCLUDED (certified)
corner       lam= 10  sum c g' >= 19.647312   W'(0) <= -10.313978   EXCLUDED (certified)
cube         lam=  4  sum c g' >= 16.062844   W'(0) <= -6.729510   EXCLUDED (certified)
strip        lam=  4  sum c g' >= 6.857070   W'(0) <= +2.476263   not excluded
corner       lam=  4  sum c g' >= 7.236143   W'(0) <= +2.097190   not excluded
```

### 25. `research/2026-11-10/window_wall_endpoints/lean_green_crosscheck/cert.py 14`

```text
strip N 14 h 1/100 sum c*secant >= 9.441756430114012 => W'(0) <= -0.10842309678067868 EXCLUDED 2.7s
corner N 14 h 1/100 sum c*secant >= 9.736836807920264 => W'(0) <= -0.40350347458693153 EXCLUDED 4.2s
```

### 26. `research/2026-11-10/window_wall_endpoints/lean_green_crosscheck/cert.py 18`

```text
strip N 18 h 1/100 sum c*secant >= 9.441756430114012 => W'(0) <= -0.10842309678067868 EXCLUDED 16.4s
corner N 18 h 1/100 sum c*secant >= 9.736836807920264 => W'(0) <= -0.40350347458693153 EXCLUDED 25.2s
```

### 27. `research/2026-11-10/window_wall_endpoints/lean_green_crosscheck/controls.py`

```text
mu 10/7 lower 3.3100399984 upper 3.310039999393303 gap 9.93303160379173e-10 | false z=E+1e-3 certified? False
mu 5/3 lower 3.6981313588 upper 3.6981313597922147 gap 9.922147167227555e-10 | false z=E+1e-3 certified? False
mu 500/301 lower 3.6894394641 upper 3.6894394651033324 gap 1.0033322088905742e-09 | false z=E+1e-3 certified? False
```

### 28. `research/2026-11-11/kyfan_chord/kyfan_plaquette.py`

```text
  1.25  2.00       5.458342  (1.2500)                   0.9578                        1.575
  0.50  1.00       3.663652  (0.5303)                   0.9159                        0.717
  1.00  1.50       4.972903  (1.0000)                   0.9696                        1.217
  1.50  2.00       5.875684  (1.5000)                   0.9840                        1.725
  0.25  4.00      -0.879828  (0.9240)                  -0.1815                        0.938

C. covers of [1/2,2] by K equal chords (uniform certified bound on the whole interval)
  K   certified min gap on [1/2,2]   exact min gap   worst cert/exact (float, 61 pts)   worst loss
  1            3.113982                 3.66807             0.6525                  34.8%
  2            3.561903                 3.66807             0.8472                  15.3%
  3            3.659476                 3.66807             0.9143                   8.6%
  6            3.668065                 3.66807             0.9710                   2.9%
 12            3.668065                 3.66807             0.9913                   0.9%

elapsed 260.4s
```

### 29. `research/2026-11-11/kyfan_chord/check_19.py`

```text
states 19 herm 1.6653345369377348e-16
0 max |diff| over all 19 levels = 1.7763568394002505e-15  E0,E1 = [0.         5.33333333]
0.1 max |diff| over all 19 levels = 1.4210854715202004e-14  E0,E1 = [0.59810737 5.88217861]
1 max |diff| over all 19 levels = 1.7763568394002505e-14  E0,E1 = [ 5.79480995 10.7258532 ]
4 max |diff| over all 19 levels = 3.552713678800501e-14  E0,E1 = [20.40829273 25.82337043]
```

### 31. `research/2026-11-11/kyfan_chord/kyfan_theta.py`

```text

E0 upper bound quality:  lam   E0_up(19-state RR)   exact E0   excess
                         0.10      0.598107      0.598107  6.43e-11
                         0.25      1.488005      1.488005  1.66e-08
                         0.50      2.950906      2.950905  1.17e-06
                         0.75      4.387039      4.387025  1.44e-05
                         1.00      5.794810      5.794723  8.66e-05
                         1.50      8.519866      8.518779  1.09e-03
                         2.00     11.119081     11.112747  6.33e-03
                         2.50     13.593965     13.570477  2.35e-02
                         3.00     15.955393     15.891178  6.42e-02
                         3.50     18.220552     18.079418  1.41e-01
                         4.00     20.408293     20.143928  2.64e-01

elapsed 74s
```

### 32. `research/2026-11-11/kyfan_certificate_grey/kyfan_cert.py`

```text
  piece [7/4, 2]: gap >= 6.24043491 for every kappa in it (exact min at kappa=7/4); claimed 624043491/100000000
  E1(kappa=1/2) <= 10.9533417771 (2-vector Rayleigh-Ritz), so gap(1/2) <= 3.6680653879
CERTIFIED: gap(kappa) >= 366806537/100000000 (= 3.66806537) for every kappa in [1/2, 2]  (exact min of the bound: 40684615689558393589631936494560539765463317453325518741/11091573214143951546431705444021135836372406295000000000 ~ 3.6680653776)
  and gap(1/2) <= 3.6680653879, so the uniform bound is tight to 1.0e-08
Controls (each must be rejected):
  rejected (as required): E0 lower bound +1/1000 at kappa=1/2
  rejected (as required): E1 lower bound +1/1000 at kappa=1/2
  rejected (as required): E0 lower bound +1/1000 at kappa=2
  rejected (as required): E1 lower bound +1/1000 at kappa=2
  rejected (as required): verifier on certificate with endpoint z0(1/2) + 1/1000
  rejected (as required): verifier on Rayleigh line lowered by 1/1000
  rejected (as required): E0 upper bound lowered by 1/1000 at each node (refuted by certified z0)
  rejected (as required): uniform gap bound raised by 1/1000 (refuted by gap(1/2) upper bound)
  rejected (as required): verifier on piece-0 claim raised by 1/1000
all 9 controls rejected.  elapsed 23.4s
```

### 33. `research/2026-11-11/kyfan_certificate_grey/b189_five_eighths.py`

```text
Step 1: C2(p,q) = |k_perp|^2/2 - |rho|^2 with |rho|^2 = 1, checked for p,q < 30
Step 1: 2 Re(tr U) chi_pq = sum of six neighbours, checked on random torus points
Step 2: H_harm psi0 = 4w psi0, H_harm psi1 = 6w psi1, <psi0,psi1> = 0, sign rep checked
Step 3: <sum phi^4>_0 = 10/omega**2   <sum phi^4>_1 = 25/omega**2
        c = (mu/24)(<.>_1 - <.>_0) = 5/8
        E0 = 4 sqrt(mu) - 1 - 5/12 + O(mu^-1/2);  E1 = 6 sqrt(mu) - 1 - 25/24 + O(mu^-1/2)
Control: doubling the quartic coefficient gives c = 5/4 != 5/8 (rejected)
Numerics: mu, E0 - (4sqrt(mu) - 1 - 5/12),  c(mu) = 2sqrt(mu) - gap,  sqrt(mu)*(c(mu) - 5/8)
  mu=   64  N= 73  E0 resid -0.00613   c=0.643036   sqrt(mu)(c-5/8)=+0.1443
  mu=  256  N= 88  E0 resid -0.00300   c=0.633715   sqrt(mu)(c-5/8)=+0.1394
  mu= 1024  N=107  E0 resid -0.00149   c=0.629286   sqrt(mu)(c-5/8)=+0.1372
  mu= 4096  N=136  E0 resid -0.00074   c=0.627126   sqrt(mu)(c-5/8)=+0.1361
```

### 34. `research/2026-11-11/ring_flux_cert/run_cert.py (L=2, cap 18)`

```text
   E0 >= 560891/100000 = 5.608910  (#neg K = 0 <= 0, disc margin 1.38e-05; float threshold 5.608924; control z+1/1000: count 1 rejected=True)
   float levels in P: [5.60892568 5.62114921 8.26505141]
 SUMMARY: gap_lo = 5.092867, floor_lo = 2.658007, floor_up = 2.658036, gap_float = 5.093210, floor_float = 2.658023

## lam = 1
 sector 0 hidden floor: d = 24741473/1250000 = 19.79318  (theta=1/20, m_Q=351/20, min E on Q = 55/3, local e0(10) >= 2803973/250000 [float 11.215894; +1/1000 rejected: True])
   RR: E0 <= 5.79471592 (exact rational; float eig 5.79471592)
   E0 >= 72433/12500 = 5.794640  (#neg K = 0 <= 0, disc margin 1.87e-05; float threshold 5.794659; control z+1/1000: count 1 rejected=True)
   E1 >= 53409/5000 = 10.681800  (#neg K = 1 <= 1, disc margin 1.68e-05; float threshold 10.681816; control z+1/1000: count 2 rejected=True)
   float levels in P: [ 5.79471592 10.68850326 10.72633281]
 sector 1 hidden floor: d = 24741473/1250000 = 19.79318  (theta=1/20, m_Q=351/20, min E on Q = 55/3, local e0(10) >= 2803973/250000 [float 11.215894; +1/1000 rejected: True])
   RR: E0 <= 8.42224818 (exact rational; float eig 8.42224818)
   E0 >= 842207/100000 = 8.422070  (#neg K = 0 <= 0, disc margin 1.16e-05; float threshold 8.422082; control z+1/1000: count 1 rejected=True)
   float levels in P: [ 8.42224818  8.47846378 11.06045492]
 SUMMARY: gap_lo = 4.887084, floor_lo = 2.627354, floor_up = 2.627608, gap_float = 4.893787, floor_float = 2.627532
```

### 35. `research/2026-11-11/ring_flux_cert/run_cert.py (L=3, cap 18)`

```text
   E0 >= 421093/50000 = 8.421860  (#neg K = 0 <= 0, disc margin 1.92e-05; float threshold 8.421879; control z+1/1000: count 1 rejected=True)
   float levels in P: [ 8.42190492  8.42315369 10.91583049]
 SUMMARY: gap_lo = 5.100544, floor_lo = 3.995504, floor_up = 3.995565, gap_float = 5.101378, floor_float = 3.995549

## lam = 1
 sector 0 hidden floor: d = 160895467/7500000 = 21.45273  (theta=3/20, m_Q=971/60, min E on Q = 55/3, local e0(10/3) >= 1463721/250000 [float 5.854885; +1/1000 rejected: True])
   RR: E0 <= 8.69216141 (exact rational; float eig 8.69216141)
   E0 >= 434597/50000 = 8.691940  (#neg K = 0 <= 0, disc margin 1.56e-05; float threshold 8.691956; control z+1/1000: count 1 rejected=True)
   E1 >= 1359409/100000 = 13.594090  (#neg K = 1 <= 1, disc margin 1.60e-05; float threshold 13.594105; control z+1/1000: count 2 rejected=True)
   float levels in P: [ 8.69216141 13.61204548 13.62118747]
 sector 1 hidden floor: d = 319027027/15000000 = 21.26847  (theta=1/10, m_Q=503/30, min E on Q = 55/3, local e0(5) >= 7503003/1000000 [float 7.503005; +1/1000 rejected: True])
   RR: E0 <= 12.66889982 (exact rational; float eig 12.66889982)
   E0 >= 1266771/100000 = 12.667710  (#neg K = 0 <= 0, disc margin 1.21e-05; float threshold 12.667722; control z+1/1000: count 1 rejected=True)
   float levels in P: [12.66889982 12.681264   15.00522463]
 SUMMARY: gap_lo = 4.901929, floor_lo = 3.975549, floor_up = 3.976960, gap_float = 4.919884, floor_float = 3.976738
```

### 36. `research/2026-11-11/ring_flux_cert/float_check.py 2 18`

```text
L=2 cap=18 sector=0 nP=520 nQ1=2984 symAB=0 t=235.7s
   lam=0.25: E0=1.488005 E1=6.697077 E2=6.701669 gap=5.209072
   lam=0.5: E0=2.950903 E1=8.044113 E2=8.056610 gap=5.093210
   lam=1.0: E0=5.794716 E1=10.688503 E2=10.726333 gap=4.893787
L=2 cap=18 sector=1 nP=487 nQ1=2849 symAB=0 t=31.0s
   lam=0.25: E0=4.152660 E1=4.155487 E2=6.816460 gap=0.002826
   lam=0.5: E0=5.608926 E1=5.621149 E2=8.265051 gap=0.012224
   lam=1.0: E0=8.422248 E1=8.478464 E2=11.060455 gap=0.056216
```

### 37. `research/2026-11-11/ring_flux_cert/float_check.py 3 18`

```text
L=3 cap=18 sector=0 nP=838 nQ1=6862 symAB=0 t=26.2s
   lam=0.25: E0=2.232007 E1=7.444532 E2=7.445388 gap=5.212524
   lam=0.5: E0=4.426356 E1=9.527734 E2=9.531003 gap=5.101378
   lam=1.0: E0=8.692161 E1=13.612045 E2=13.621187 gap=4.919884
L=3 cap=18 sector=1 nP=819 nQ1=6971 symAB=0 t=5.6s
   lam=0.25: E0=6.231039 E1=6.231178 E2=8.812194 gap=0.000138
   lam=0.5: E0=8.421905 E1=8.423154 E2=10.915830 gap=0.001249
   lam=1.0: E0=12.668900 E1=12.681264 E2=15.005225 gap=0.012364
```

### 38. `research/2026-11-11/su3_twosquare/test_small.py`

```text
ECUT=13.333333334333334 K=None states=19 pairs=19 nnz=92 hw 0.1s total 0.1s
ECUT=40/3 0 [0.         5.33333333 5.33333333]
ECUT=40/3 0.1 [0.59810737 5.88217861 5.88226917]
ECUT=40/3 1 [ 5.79480995 10.7258532  10.72670225]
ECUT=40/3 4 [20.40829273 25.82337043 26.83384014]
ECUT=10000.0 K=3 states=367 pairs=100 nnz=7208 hw 0.2s total 0.5s
K=3 1 [ 5.79472341 10.71474377 10.72527103]
K=3 4 [20.14485725 25.35698114 25.52277948]
```

### 39. `research/2026-11-11/su3_twosquare/check_recoupling.py`

```text
1. GT relations max err 7.105427357601002e-14
2. sum N_a d_a - d_b d_c max 0
3. recoupling R orthogonality: 112 blocks (b,c,a'), max |R R^T - 1| = 2.66e-15
```

### 43. `research/spectrum_strip_corner_2026_11_11/dump_dcube.py`

```text
dimension 95 faces 11 edges 20 seconds 212.1
```

### 44. `research/spectrum_strip_corner_2026_11_11/dcube_test_b.py`

```text
  0.98       31.418791    31.477071    -0.058280 0.998148
  0.9867     31.628498    31.628462    +0.000036 1.000001
  1.0        32.044640    31.928984    +0.115656 1.003622
  1.25       39.835533    37.577897    +2.257636 1.060079
  1.5        47.578492    43.226809    +4.351683 1.100671
  2.0        62.969709    54.524635    +8.445075 1.154885
  3.0        93.553214    77.120285   +16.432929 1.213082
sign changes of lambda_min - U on (0.01, 5]: [(np.float64(0.98), np.float64(0.99))]
Reading 1 crossing lam* ~ 0.986695893; exact LDL: neg pivots of A-U at 0.986695 = 1, at 0.986697 = 0
control: exclusion claimed at lam=1/2 (A-U PSD) -> neg pivots 1: REJECTED (ok)
ratios lambda_min/U at lam=1, 1/2: 1.0036222880647836 0.7872632244193007
reading 3 (lambda_2 = U) sign changes: [(np.float64(0.4), np.float64(0.41))]
reading 5 (retained at lam/2) sign changes: []
(33-K) I - S: negative pivots = 0 (0 => positive definite => exclusion holds for every lam >= the upper bracket end)
control: (5/2) I - S claimed PSD -> negative pivots = uncertified pivot (not accepted): REJECTED (ok)
```

### 45. `research/spectrum_strip_corner_2026_11_11/strip_corner_crossing.py`

```text
   EXCLUDED (certified) at lam = 5213413/1000000 = 5.213413:  L_lower = 1.0000001562 > t = 1  (margin 1.562e-07)
   secant test cannot exclude at lam = 521341/100000 = 5.21341:  L_upper = 0.9999998144 <= t  (margin 1.856e-07)
   control: strip h=c/1000: exclusion at lam_lo=5.21341: claim holds = False -> REJECTED (ok)
   control: strip h=c/1000: exclusion at lam_hi with t raised by 1/1000: claim holds = False -> REJECTED (ok)
   control: strip h=c/1000: exclusion at lam_hi against the pre-vertex-rule upper t = 36/35: claim holds = False -> REJECTED (ok)
corner: c = 3, t = 10/9, h = c/1000
   lam=5: L_lower = 1.083426
   lam=5.25: L_lower = 1.149423
   float crossing lam* ~ 5.104163887
   EXCLUDED (certified) at lam = 1020833/200000 = 5.104165:  L_lower = 1.1111112054 > t = 10/9  (margin 9.426e-08)
   secant test cannot exclude at lam = 5104163/1000000 = 5.104163:  L_upper = 1.1111110766 <= t  (margin 3.453e-08)
   control: corner h=c/1000: exclusion at lam_lo=5.104163: claim holds = False -> REJECTED (ok)
   control: corner h=c/1000: exclusion at lam_hi with t raised by 1/1000: claim holds = False -> REJECTED (ok)
   control: corner h=c/1000: exclusion at lam_hi with the strip coefficient c = 10/3 swapped in against t = 10/9: claim holds = False -> REJECTED (ok)
all controls rejected as required
```

### 47. `scripts/verify.py --gate-only`

```text
OK (gate only): no banned tokens, 1201 frozen statements match
```

## Counts that differ from the documents

1. `research/2026-11-11/kyfan_certificate_grey/README.md` says "There are 25 finite-support rational trial vectors". `kyfan_cert.py` (shipped `kyfan_cert.out` and this rerun) prints "26 rational trial vectors". The script output and the README disagree; the README is the one that differs.
2. `research/window_wall_2026_11_10/varying_s/varying_s_lp.py` prints a strip bound t* <= 1.02857 (36/35, before the vertex-rule labellings). `varying_s/README.md` gives the strip t as 1. The README value comes from `strip_settle.py` and `strip_lower.py`, which print t = 1 and match. Not a count error, but the LP output does not show the t = 1 figure.
3. `varying_s/README.md` describes the double-cube LP as "a weighted mixture of 19 seven-link thetas". The script prints "trial states=1449" for that cell. These are different quantities, so they cannot be compared directly.
4. `spectrum_strip_corner_2026_11_11/README.md` and `dump_dcube` timing: README says dump_dcube takes "~9 min"; this run took 212 s (wall 215 s). Timing only, not a count.
5. `kyfan_chord/README.md` says a single chord [0,4] is "positive only up to lambda ~ 2.4". The printed table shows +0.530 at lambda 2.00 and -0.061 at lambda 2.50, so the crossing lies between them. The value 2.4 itself is not printed. Not contradicted, not confirmed.
6. No other printed number disagrees with its nearby README or report. Checked and matching: 13587 / 20 / 2275 (paper README and reports/01); 58 targets split 14/14/14/10/6 (cross_theorem README and REPORT, "52 + 6"); 4.908928 (reports/04, Lean README); window-wall margins 1.4512, 0.1241, 0.4204, 2.0306, 2.5889 (cells README); U = -1.9484e-5 (dcube README); strip 5.213413 and corner 5.104165 crossings (spectrum README); dcube lambda* bracket (0.986695, 0.986697]; ring L=2 and L=3 gap and floor values (ring README table); kyfan_theta 1/4-node cover values (kyfan_chord README); 19-state values at lambda=1 and 4 (su3_twosquare README); GT error 7.11e-14 and 112 blocks (su3_twosquare README).

## Notes on the run

- `sympy` was not installed. Installed with `pip install --break-system-packages sympy` (1.14.0), as the harness allows. `run_all.py` first exited 1 for that reason (log overwritten by the rerun).
- `certify_slopes.py` under `research/2026-11-10/window_wall_endpoints/` hardcodes `/workspace/yang-mills-lean/research/yang_mills_2026_09_09` (line 10). That path is absent here, so the file as shipped fails. A supplementary copy in a scratch folder, with only that path line replaced, reproduces the shipped `certify_slopes_N28.out` exactly. The repo file was not edited.
- `recheck.py` created `research/yang_mills_2026_09_09/cross_theorem/native/fresh_evidence_verifier` in the working copy (the output directory must not exist beforehand).
- Scripts that write into their own folder overwrote outputs in the working copy. Shipped originals were backed up first: `out/verifier/p3_orig_backup/` (window-wall folders), `out/verifier/p4_orig_backup/` (2026-11-11 and spectrum folders). `certify_slopes_N20.json` in the window-wall root and `dcube_S.json` (rebuilt by `dump_dcube.py`) were written in the working copy as well.
- Rerun outputs match the shipped `.out` files line for line apart from timing lines, with two exceptions noted in the table: `kyfan_cert.py` (trailing "exit 0" line appears only in the shipped file) and `kyfan_theta.py` (one timing line).
- Not run, by instruction: `theta_reference.py` (README: about 15 min); `su3_twosquare/run_sweep.py`, `run_ecut300_lam64.py`, `run_ecut300_lam128.py`. Not on the task list and not run: `paper/2026-09-08` other folders, `research/yang_mills_2026_09_09/scripts/su3_character_certificate.py`, and the other `su3_twosquare` scripts.
- `scripts/verify.py` full mode was not run: it needs `lake`/`lean`, which are not on this machine; the `--gate-only` mode was run because it is the documented no-Lean path.
