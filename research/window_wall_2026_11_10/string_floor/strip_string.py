# Source (+1 triality) at u, sink (-1) at v on strip/corner/cube: minimal fundamental support vs graph distance.
import sys
from itertools import combinations, product
from collections import deque
import os
from pathlib import Path
HERE = Path(__file__).resolve().parent
# repo root is three levels up (research/window_wall_2026_11_10/<folder>/); YM_RESEARCH overrides
YM = os.environ.setdefault('YM_RESEARCH', str(HERE.parents[2] / 'research' / 'yang_mills_2026_09_09'))
for p in ('/scripts','/cross_theorem/scripts','/cross_theorem/native'): sys.path.insert(0,YM+p)
import spatial_gauge as sg
def ok(S,es,u,v):
    for o in product((0,1),repeat=len(S)):
        net={}
        for i,b in zip(S,o):
            a,c=es[i] if b==0 else es[i][::-1]
            net[a]=net.get(a,0)+1; net[c]=net.get(c,0)-1
        want=lambda x: 1 if x==u else (-1 if x==v else 0)
        if all((net.get(x,0)-want(x))%3==0 for x in set(net)|{u,v}): return True
    return False
for name in ('strip','corner','cube'):
    m=sg.model(name); es=m['edges']; V=sorted({x for e in es for x in e}); bad=0
    adj={x:[] for x in V}
    for a,b in es: adj[a].append(b); adj[b].append(a)
    for u,v in combinations(V,2):
        dist={u:0}; q=deque([u])
        while q:
            x=q.popleft()
            for y in adj[x]:
                if y not in dist: dist[y]=dist[x]+1; q.append(y)
        k=next(k for k in range(1,len(es)+1) if any(ok(S,es,u,v) for S in combinations(range(len(es)),k)))
        if k!=dist[v]: bad+=1; print(name,u,v,'min',k,'dist',dist[v])
    print(name,'pairs',len(V)*(len(V)-1)//2,'mismatches',bad)
