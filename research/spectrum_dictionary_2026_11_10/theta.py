from fractions import Fraction as F
from itertools import product
from collections import Counter
def cas(p,q): return F(p*p+p*q+q*q+3*p+3*q,3)
def weights(p,q):
    # GT patterns for highest weight (p+q, q, 0)
    l1,l2,l3=p+q,q,0; W=Counter()
    for a in range(l2,l1+1):
        for b in range(l3,l2+1):
            for c in range(b,a+1):
                r1=c; r2=a+b-c; r3=l1+l2+l3-a-b
                # Dynkin weight (r1-r2, r2-r3)
                W[(r1-r2,r2-r3)]+=1
    return W
def tensor(A,B):
    res=Counter()
    for (m1,m2),mult in weights(*B).items():
        x,y=A[0]+m1+1,A[1]+m2+1; s=1
        # reflect into dominant chamber (rho-shifted)
        for _ in range(10):
            if x<0: y+=x; x=-x; s=-s
            elif y<0: x+=y; y=-y; s=-s
            else: break
        if x==0 or y==0: continue
        res[(x-1,y-1)]+=s*mult
    return {k:v for k,v in res.items() if v}
N=7
irr=[(p,q) for p in range(N) for q in range(N) if p+q<N]
assert tensor((1,0),(1,0))=={(2,0):1,(0,1):1}
assert tensor((1,0),(0,1))=={(1,1):1,(0,0):1}
assert tensor((1,1),(1,1))=={(2,2):1,(3,0):1,(0,3):1,(1,1):2,(0,0):1}
E=Counter()
for A,B,C in product(irr,repeat=3):
    if (A,B,C)==((0,0),)*3: continue
    if (C[1],C[0]) in tensor(A,B):
        e=cas(*A)+3*cas(*B)+3*cas(*C)
        if e<=17: E[e]+=1; 
        if e<=17: print(float(e),e,A,B,C)
print(sorted(set(E)))
