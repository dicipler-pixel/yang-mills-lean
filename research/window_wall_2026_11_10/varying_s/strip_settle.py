# Add every fundamental labelling realizable by an orientation with (in-out) = 0 mod 3 at each vertex
# (3x3bar, 3x3x3, 3x3x3barx3bar all contain the singlet), then redo the exact upper bound on t for the strip.
import sys
from itertools import combinations, product
from fractions import Fraction as F
import os
from pathlib import Path
HERE = Path(__file__).resolve().parent
# repo root is three levels up (research/window_wall_2026_11_10/<folder>/); YM_RESEARCH overrides
YM = os.environ.setdefault('YM_RESEARCH', str(HERE.parents[2] / 'research' / 'yang_mills_2026_09_09'))
for p in ('/scripts','/cross_theorem/scripts','/cross_theorem/native'): sys.path.insert(0,YM+p)
import spatial_gauge as sg, numpy as np
from scipy.optimize import linprog
def realizable(S,es):
    for o in product((0,1),repeat=len(S)):
        net={}
        for i,b in zip(S,o):
            a,c=es[i] if b==0 else es[i][::-1]
            net[a]=net.get(a,0)+1; net[c]=net.get(c,0)-1
        if all(v%3==0 for v in net.values()): return True
    return False
for name in ('strip','corner'):
    m=sg.model(name); es=m['edges']; E=len(es)
    states=[]
    for k in range(7,E+1):
        for S in combinations(range(E),k):
            if realizable(S,es): states.append({i:F(4,3) for i in S})
    for k in (4,6):
        for S in combinations(range(E),k):
            d={}
            for i in S:
                for v in es[i]: d[v]=d.get(v,0)+1
            if set(d.values())=={2}: states.append({i:F(3) for i in S})
    n=len(states); M=np.array([[float(s.get(e,0)) for s in states] for e in range(E)])
    res=linprog(np.r_[np.zeros(n),1],A_ub=np.c_[M,-np.ones(E)],b_ub=np.zeros(E),A_eq=np.r_[np.ones(n),0][None,:],b_eq=[1],bounds=[(0,None)]*(n+1),method='highs')
    mu=[F(x).limit_denominator(10**6) if x>1e-12 else F(0) for x in res.x[:n]]; mu=[x/sum(mu) for x in mu]
    t=max(sum(mu[j]*states[j].get(e,0) for j in range(n)) for e in range(E))
    used=[(sorted(states[j]),str(mu[j])) for j in range(n) if mu[j]]
    print(name,'states',n,'exact upper t =',t,float(t)); print('  mixture:',used)
