# Strip/corner crossings under link-dependent s, and GPT's double-cube test (b) (Spectrum, 2026-11-11)

Jeromie N. Beasley · GitHub dicipler-pixel · X @d1c1pler · YouTube @AtlasMemoriae ·
atlas-memoriae.dicipler.workers.dev · ORCID https://orcid.org/0009-0006-4645-5643

Scope: strong-coupling window-wall bookkeeping on finite cells (C <= 8 complete-tail class).
No continuum claim, no mass-gap claim. Branch `spectrum-strip-corner` off main 3422e89, not pushed.

## 1. Strip and corner in (5, 5.25] (`strip_corner_crossing.py` -> `.out`, `.json`)

Test exactly as in `../window_wall_2026_11_10/varying_s/` (`lambda_scan.py` / `exact_t.py`):
excluded when L(c) > t, with L(c) = (g_lo(c+h) - g_up(c))/h, h = c/1000, c = E/P, and g_lo/g_up
loaded verbatim from `certify_slopes.py` (repo `interval_inertia`, N = 24, EPS = 1e-10; exact
integer-interval acceptance). t = 1 (strip, settled two-sided by `strip_settle.py`/`strip_lower.py`),
t = 10/9 (corner). Floats only propose the crossing; every decision is exact.

| cell | c | t | not excluded by this test at (certified upper bound on the secant <= t) | **excluded (certified L > t) from** |
|---|---|---|---|---|
| strip | 10/3 | 1 | lambda = 5.213410 (L_up = 0.99999981) | **lambda = 5.213413** (L_lo = 1.00000016) |
| corner | 3 | 10/9 | lambda = 5.104163 (L_up = 1.11111108) | **lambda = 5.104165** (L_lo = 1.11111121) |

Float crossings: strip 5.2134116, corner 5.1041639. `WindowWallMono.forward_secant_mono` (forward
secant nondecreasing in lambda; concavity of e on [0, inf) is a hypothesis there) carries each
exclusion to every larger lambda, so with lambda_scan's points this closes (5, 5.25] for both cells.
Also reproduces lambda_scan/exact_t: L(5) = 0.946761 / 1.083426, L(5.25) = 1.009035 / 1.149423.

Controls that must fail (all rejected): exclusion at the lower bracket end; exclusion at the
upper end with t raised by 1/1000; strip against the pre-vertex-rule t = 36/35; corner with the
strip coefficient c = 10/3 swapped in; certify_slopes' wrong E upper/lower endpoints at mu = 5/2.

Note: these are the crossings of the h = c/1000 secant test. The true derivative g'(c) is >= the
secant, so the true crossings are a little lower; a smaller-h run (h = c/10^5) was too slow to
bracket this session and is left open.

## 2. GPT's double-cube test (b) (`dump_dcube.py`, `dcube_test_b.py` -> `.out`, `.json`)

The 95 x 95 matrix is the repo's `spatial_certificates.retained(m, d, lam)` for `spatial_gauge`
model `double_cube`: 95 = 1 + 2 x (11 squares + 36 hexagons), A(lam) = diag(E_i) + 33 lam - lam S.
`dump_dcube.py` builds S exactly (repo `calculate`, ~9 min) and caches it in `dcube_S.json`.

Reading that reproduces: 0.9867 is the coupling where lambda_min(A(lam)) = U(lam).
- Float crossing lam* = 0.98669589.
- Exact interval LDL of A(lam) - U(lam) I: one negative pivot at lam = 0.986695, zero at 0.986697.
  So lambda_min(A) >= U for lam >= 0.986697 (checked at that endpoint) and < U at 0.986695.
- Consistency: the stored double-cube targets at lam = 1/10 and 1/2 have r just above lambda_min(A)
  and d <= U(lam) (at 1/2: d = 20.603685 <= U = 20.631159), i.e. "certificate accepted at 0.5".
- Control: claiming exclusion at lam = 1/2 (A - U PSD) is rejected (1 negative pivot).
- Other readings tried and rejected: lambda_2(A) = U crosses near 0.40; retained matrix at lam/2
  never crosses on (0, 5]; the ratio lambda_min/U is 0.787 at 1/2 and 1.0036 at 1, not 0.9867.

Verdict: the number 0.9867 reproduces (bracket (0.986695, 0.986697]). What does NOT reproduce here:
where U's slope 20541500575676903/909090909514080 (= 33 - 10.4043494) comes from. It looks like a
rationalized float; it has to be a true upper bound on the omitted-sector (C > 8) minimum for the
test to exclude anything, and that trial state is not in the repo. Until it is, test (b) is
"reproduced given U", and the double-cube exclusion relied on stays (a), from 1.7347717.
All larger lambda: A(lam) - U(lam) I = (diag(E) - 28/3) + lam((33 - K) I - S) is affine in lam, so
f(lam) = lambda_min(A) - U is concave with f' >= lambda_min((33 - K) I - S). Exact LDL shows
(33 - K) I - S positive definite (sigma_max(S) = 2.670 < 33 - K = 10.404), so f is increasing and
f >= 0 for every lam >= 0.986697. Control: (5/2) I - S is not certified PSD (float lambda_min ~ -0.17;
the interval LDL refuses it with an uncertified pivot).

## Run

    python3 strip_corner_crossing.py   # ~6 min
    python3 dump_dcube.py              # ~9 min, writes dcube_S.json (committed)
    python3 dcube_test_b.py            # ~7 s
