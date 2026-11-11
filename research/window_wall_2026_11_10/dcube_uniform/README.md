# Double-cube uniform wall at the exclusion endpoint (Green, 2026-11-10)

Certifies the window-wall test for the double cube with the uniform (Jensen)
split c_p = 20/11 on all 11 faces (sum 20, alpha = 1), at the single
exclusion endpoint lambda/alpha = 17347717/10^7 = 1.7347717.

`certify_dcube_uniform.py` -> `certify_dcube_uniform.out`, `certify_dcube_uniform.json`

Method (same as `../dcube_edge/` and `../endpoints/certify_slopes.py`):
exact rationals, repo `interval_inertia` with the Schur tail matrix and
Rayleigh–Ritz, N = 24, EPS = 1e-11, h = 1/10^5. Forward secant

    U = 28/3 - sum_p c_p (g_lo(c_p+h) - g_up(c_p))/h  >= W'(0).

U <= 0 implies exclusion (`WindowWallFinite`). Wrong upper and lower
endpoint controls at mu = 5/2 were rejected.

## Result

Certified U = -4435334032736196355095411672194503 / 227640311408488358377099027485000000000
= -1.9483956972705184e-5 <= 0. Slack (how far U is below 0) is this same margin.
Matches the earlier `run_edge_c2011` float at this point.

## Coverage of all larger lambda

No grid is used. `WindowWallMono.forward_secant_mono` (merged; also
WINDOW_WALL.md) says the true forward secant g(c+h, lam) - g(c, lam) is
nondecreasing in lam, because e in g(kappa, lam) = kappa e(lam/kappa) is
concave on [0, inf). So U_true is nonincreasing in lam, and a certified
exclusion at 1.7347717 holds at every larger coupling for the same graph
and allocation. Concavity of e is a hypothesis of that lemma.

Red's Jensen argument makes this c = 20/11 wall uniform over all splits:
every split of the double cube is excluded from lambda/alpha = 1.7347717 up.

## Caveats

- This is an outer bound on certificates of this class (total-electric
  cutoff C <= 8, floor 28/3). It excludes; it does not locate the true
  spectral edge.
- The formalized h = 1/1000 test only excludes later (from 1.7352404).
  The tighter h = 1e-5 is required for this endpoint.
- GPT's 0.9867 figure is a different test and is not used here.
