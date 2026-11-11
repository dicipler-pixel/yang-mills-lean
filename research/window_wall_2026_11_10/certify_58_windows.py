# Exact check that every stored target obeys d - r <= W(s), with W bounded BELOW by certified endpoints:
#   W(s) >= s*28/3 - sum_p [ g_up(c_p) - g_lo((1-s)c_p) ]   (g(0)=0 exactly)
import sys
sys.argv = ['x', sys.argv[1] if len(sys.argv) > 1 else '20']
src = open('certify_slopes.py').read().split("cases = [")[0]
exec(src)
from targets import all_targets
from fractions import Fraction as F
worst = None; n = 0; viol = 0
for name, rows in all_targets().items():
    coef = sc.allocation_coeffs(sg.model(name))
    for t in rows:
        lam, s, d, r = F(t['lambda']), F(t['s']), F(t['d']), F(t['r'])
        Wlo = s * F(28, 3) - sum(g_up(c, lam) - (g_lo((1 - s) * c, lam) if s < 1 else 0) for c in coef)
        slack = Wlo - (d - r); n += 1; viol += slack < 0
        if worst is None or slack < worst[0]: worst = (slack, name, t['lambda'], t['s'])
print(f'targets checked: {n}, violations: {viol}')
print(f'smallest certified slack: {float(worst[0]):.9f} at {worst[1]} lam={worst[2]} s={worst[3]}')
