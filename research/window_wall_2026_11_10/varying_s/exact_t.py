# Exact two-sided bounds on t* = max_s min_tail <s,C>/sum(s) for strip and corner (and others),
# plus exact L comparison. Upper: rational mixture of realizable tail labellings
# (fund cycles>=8, fund thetas>=7 via 3x3x3 singlet, adjoint 4/6-cycles, theta with one adjoint arm (3,3bar,8),
#  theta with one sextet arm (3,3,6bar), dumbbells: fund loops + adjoint bridge).
# Lower: for the LP's optimal s (rationalized), min over ALL leaf-free supports S:
#  |S|>=7 -> (4/3)s(S); |S|<=6 (single cycle, non-fund irrep, C2>=3) -> 3 s(S).
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
FU,AD,SX=F(4,3),F(3),F(10,3)
def comps(S,es):
    adj={}
    for i in S:
        a,b=es[i]; adj.setdefault(a,set()).add(b); adj.setdefault(b,set()).add(a)
    if not adj: return 0
    seen=set();n=0
    for s in adj:
        if s in seen: continue
        n+=1;st=[s];seen.add(s)
        while st:
            v=st.pop()
            for u in adj[v]:
                if u not in seen: seen.add(u); st.append(u)
    return n
def degs(S,es):
    d={}
    for i in S:
        for v in es[i]: d[v]=d.get(v,0)+1
    return d
def arms(S,es,d):
    # for a theta/dumbbell: split edges into paths between degree-3 vertices
    b=[v for v in d if d[v]==3]; inc={}
    for i in S:
        for v in es[i]: inc.setdefault(v,[]).append(i)
    out=[];used=set()
    for v0 in b:
        for e0 in inc[v0]:
            if e0 in used: continue
            path=[e0];used.add(e0);v=es[e0][0] if es[e0][1]==v0 else es[e0][1]
            while d[v]==2:
                e=[x for x in inc[v] if x not in used][0];used.add(e);path.append(e)
                v=es[e][0] if es[e][1]==v else es[e][1]
            out.append((path,v0,v))
    return out
def run(name,lams):
    m=sg.model(name); es=m['edges']; E=len(es); P=len(m['faces'])
    states=[]; allsupp=[]
    for k in range(1,E+1):
        for S in combinations(range(E),k):
            d=degs(S,es)
            if min(d.values())<2: continue
            allsupp.append(S)
            if comps(S,es)!=1: continue
            ds=list(d.values())
            if set(ds)=={2}:
                states.append({i:(FU if k>=8 else AD) for i in S})
                if k in(4,6) and k>=8: pass
                if k in (4,6) : pass
            elif sorted(ds).count(3)==2 and max(ds)==3:
                A=arms(S,es,d)
                bridge=[a for a in A if a[1]==a[2]]
                if not bridge and k>=7: states.append({i:FU for i in S})   # baryon theta
                if not bridge:
                    for j in range(3):  # one adjoint arm / one sextet arm
                        for R in (AD,SX):
                            st={i:FU for i in S}
                            for i in A[j][0]: st[i]=R
                            if sum(st.values())>8: states.append(st)
                else:
                    # dumbbell: loops fund, the non-loop path adjoint
                    st={i:FU for i in S}
                    for a in A:
                        if a[1]!=a[2]:
                            for i in a[0]: st[i]=AD
                    if sum(st.values())>8: states.append(st)
    # adjoint short cycles already added (k<8 cycles -> AD)
    states=[s for s in states if sum(s.values())>8]
    n=len(states); M=np.array([[float(s.get(e,0)) for s in states] for e in range(E)])
    res=linprog(np.r_[np.zeros(n),1],A_ub=np.c_[M,-np.ones(E)],b_ub=np.zeros(E),A_eq=np.r_[np.ones(n),0][None,:],b_eq=[1],bounds=[(0,None)]*(n+1),method='highs')
    mu=[F(x).limit_denominator(10**6) if x>1e-12 else F(0) for x in res.x[:n]]; tot=sum(mu); mu=[x/tot for x in mu]
    t_up=max(sum(mu[j]*states[j].get(e,0) for j in range(n)) for e in range(E))
    y=-res.ineqlin.marginals  # dual: weights on links
    s=[F(max(v,0)).limit_denominator(10**6) for v in y]; ts=sum(s); s=[v/ts for v in s]
    t_lo=min((FU if len(S)>=7 else AD)*sum(s[i] for i in S) for S in allsupp)
    print(f"{name}: states={n} t_upper={t_up} ({float(t_up):.6f}) t_lower={t_lo} ({float(t_lo):.6f})",flush=True)
    cc=F(E,P); h=cc/1000
    for l in lams:
        L=(g_lo(cc+h,F(l))-g_up(cc,F(l)))/h
        print(f"   lam={l} mu=lam/c={float(F(l)/cc):.4f} L={float(L):.6f} excluded(L>t_upper)={L>t_up}",flush=True)
run('strip',['5','5.25','5.5','5.75','6'])
run('corner',['5','5.25','5.5','5.75','6'])
run('two',['8']); run('cube',['3'])
