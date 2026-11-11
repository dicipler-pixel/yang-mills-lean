import sys
from fractions import Fraction as F
sys.argv=['x','24']
import os
from pathlib import Path
HERE = Path(__file__).resolve().parent
# repo root is three levels up (research/window_wall_2026_11_10/<folder>/); YM_RESEARCH overrides
YM = os.environ.setdefault('YM_RESEARCH', str(HERE.parents[2] / 'research' / 'yang_mills_2026_09_09'))
exec(open(HERE.parent / 'certify_slopes.py').read().split("# failure control")[0])
for name,E,P,t,lams in [('strip',10,3,1.02857,[6,7,8,10,12]),('corner',9,3,1.11111,[6,7,8,10])]:
    cc=F(E,P); h=cc/1000
    for l in lams:
        L=float((g_lo(cc+h,F(l))-g_up(cc,F(l)))/h); print(name,l,round(L,5),'excluded' if L>t else 'not')
