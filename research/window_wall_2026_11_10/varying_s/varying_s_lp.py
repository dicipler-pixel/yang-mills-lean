import sys
from itertools import combinations
from fractions import Fraction as F
import os
from pathlib import Path
HERE = Path(__file__).resolve().parent
# repo root is three levels up (research/window_wall_2026_11_10/<folder>/); YM_RESEARCH overrides
YM = os.environ.setdefault('YM_RESEARCH', str(HERE.parents[2] / 'research' / 'yang_mills_2026_09_09'))
for p in ('/scripts','/cross_theorem/scripts','/cross_theorem/native'): sys.path.insert(0,YM+p)
import spatial_gauge as sg
import numpy as np
from scipy.optimize import linprog
sys.argv=['x','24']
exec(open(HERE.parent / 'certify_slopes.py').read().split("# failure control")[0])
lamd={'two':8,'strip':5,'corner':5,'cube':3,'double_cube':2}
def conn(S,es):
    adj={}
    for i in S:
        a,b=es[i]; adj.setdefault(a,set()).add(b); adj.setdefault(b,set()).add(a)
    st=[next(iter(adj))]; seen=set(st)
    while st:
        v=st.pop()
        for u in adj[v]:
            if u not in seen: seen.add(u); st.append(u)
    return len(seen)==len(adj)
for name in lamd:
    m=sg.model(name); es=m['edges']; E=len(es); P=len(m['faces'])
    states=[]
    for k in range(7,min(E,12)+1):
        for S in combinations(range(E),k):
            deg={}
            for i in S:
                for v in es[i]: deg[v]=deg.get(v,0)+1
            ds=list(deg.values())
            if min(ds)<2 or max(ds)>3: continue
            n3=ds.count(3)
            if n3==0 and k>=8 and conn(S,es): states.append(S)
            elif n3==2 and conn(S,es) and all(conn(tuple(j for j in S if j!=i),es) for i in S): states.append(S)
    adj=[]
    for k in (4,6):
        for S in combinations(range(E),k):
            deg={}
            for i in S:
                for v in es[i]: deg[v]=deg.get(v,0)+1
            if set(deg.values())=={2} and conn(S,es): adj.append(S)
    A=np.zeros((E,len(states)+len(adj)))
    for j,S in enumerate(states):
        for i in S: A[i,j]=4/3
    for j,S in enumerate(adj):
        for i in S: A[i,len(states)+j]=3
    states=states+adj
    n=len(states); c=np.r_[np.zeros(n),1]
    res=linprog(c,A_ub=np.c_[A,-np.ones(E)],b_ub=np.zeros(E),A_eq=np.r_[np.ones(n),0][None,:],b_eq=[1],bounds=[(0,None)]*(n+1),method='highs')
    t=res.fun
    lam=F(lamd[name]); cc=F(E,P); h=cc/1000
    L=float((g_lo(cc+h,lam)-g_up(cc,lam))/h)
    print(f"{name}: E={E} trial states={n} t*<={t:.5f} (uniform 28/3/E={28/3/E:.5f}) L={L:.5f} margin L-t={L-t:.5f} excluded={L>t}",flush=True)
