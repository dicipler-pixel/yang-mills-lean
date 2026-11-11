import sys
from itertools import combinations
from fractions import Fraction as F
import os
from pathlib import Path
HERE = Path(__file__).resolve().parent
# repo root is three levels up (research/window_wall_2026_11_10/<folder>/); YM_RESEARCH overrides
YM = os.environ.setdefault('YM_RESEARCH', str(HERE.parents[2] / 'research' / 'yang_mills_2026_09_09'))
for p in ('/scripts','/cross_theorem/scripts','/cross_theorem/native'): sys.path.insert(0,YM+p)
import spatial_gauge as sg, numpy as np
from scipy.optimize import linprog
m=sg.model('strip'); es=m['edges']; E=len(es)
sup=[]
for k in range(1,E+1):
    for S in combinations(range(E),k):
        d={}
        for i in S:
            for v in es[i]: d[v]=d.get(v,0)+1
        if min(d.values())>=2: sup.append(S)
rows=[]
for S in sup:
    w=4/3 if len(S)>=7 else 3
    r=np.zeros(E); r[list(S)]=w; rows.append(r)
R=np.array(rows)
# max t: R s >= t, sum s=1
res=linprog(np.r_[np.zeros(E),-1],A_ub=np.c_[-R,np.ones(len(R))],b_ub=np.zeros(len(R)),A_eq=np.r_[np.ones(E),0][None,:],b_eq=[1],bounds=[(0,None)]*E+[(None,None)],method='highs')
s=[F(x).limit_denominator(1000) for x in res.x[:E]]; s=[x/sum(s) for x in s]
tl=min((F(4,3) if len(S)>=7 else F(3))*sum(s[i] for i in S) for S in sup)
print('edges',es); print('s',[str(x) for x in s]); print('exact lower t',tl,float(tl))
