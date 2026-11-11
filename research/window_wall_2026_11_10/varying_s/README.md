# Link-dependent retained fraction s (Grey, 2026-11-10)

Scripts by Grey, rechecked exactly by Green. They bound the window-wall test when the
retained electric fraction s varies from link to link:

    d - r <= s_bar E (t - L(c)),   t = max_s min_tail <s, C> / sum(s).

A cell is excluded when L(c) > t. This uses r >= P g(c), so failing to exclude is a limit of
the bound, not evidence that a window opens.

Exact t values: two squares 4/3, cube 7/9, double cube 7/15, corner 10/9, strip 1.

| script | output | what it does |
|---|---|---|
| `exact_t.py` | `exact_t.out` | exact two-sided bounds on t and the exact L comparison. Strip upper 36/35 here, before the vertex-rule labellings are added |
| `strip_settle.py` | `strip_settle.out` | adds every labelling allowed by the vertex rule (in - out = 0 mod 3); strip upper t = 1 (mixture 1/4 each: two 7-link thetas, outer 8-cycle, pair of end squares); corner 10/9 |
| `strip_lower.py` | `strip_lower.out` | matching exact lower bound t >= 1 for the strip |
| `varying_s_lp.py` | `varying_s_lp.out` | LP over all five cells (double cube 7/15, a weighted mixture of 19 seven-link thetas) |
| `lambda_scan.py` | `lambda_scan.out` | strip and corner at larger lambda |

Outcome: two squares (lambda = 8), cube (3) and double cube (2) stay excluded. Strip and
corner are not excluded at lambda = 5 by this bound but are excluded at 5.25 (L = 1.009 > 1
and 1.149 > 10/9), so both close somewhere in (5, 5.25].

Run from this folder with `python3 <script>.py`. The scripts find
`research/yang_mills_2026_09_09` relative to the repo (override with `YM_RESEARCH`) and use
`../certify_slopes.py`. Rerun from a repo-shaped tree, each output is byte-identical to
running Grey's originals.
