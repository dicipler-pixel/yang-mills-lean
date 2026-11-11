from math import comb
E_=[(0,4),(0,2),(0,1),(1,5),(1,3),(2,6),(2,3),(3,7),(4,8),(4,6),(4,5),(5,9),(5,7),(6,10),(6,7),(7,11),(8,10),(8,9),(9,11),(10,11)]
L=lambda l:'['+','.join(f'({a},{b})' for a,b in l)+']'
out=[];n=[0]
import sys
LIM=int(sys.argv[1]) if len(sys.argv)>1 else 600
def st(k,es,acc): return f'allChoose hypB {k} {L(es)} {L(acc)} = true'
def go(k,es,acc):
    n[0]+=1; name=f'dc{n[0]}'
    if k==0 or len(es)<k or comb(len(es),k)<=LIM:
        out.append(f'set_option maxRecDepth 100000 in\ntheorem {name} : {st(k,es,acc)} := by decide +kernel\n'); return name
    e,rest=es[0],es[1:]
    a=go(k-1,rest,acc+[e]); b=go(k,rest,acc)
    out.append(f'theorem {name} : {st(k,es,acc)} := by\n  rw [show allChoose hypB {k} {L(es)} {L(acc)} = (allChoose hypB {k-1} {L(rest)} {L(acc+[e])} && allChoose hypB {k} {L(rest)} {L(acc)}) from rfl, {a}, {b}]; rfl\n')
    return name
roots=[go(k,E_,[]) for k in range(1,7)]
hdr='import TailFloor\nnamespace TailFloor\n'
body=''.join(out)
top='theorem dcube_checkB : checkB dcubeE = true := by\n  unfold checkB\n  rw [show List.range 6 = [0,1,2,3,4,5] from rfl]\n  simp only [List.all_cons, List.all_nil, dcubeE, Nat.reduceAdd, '+', '.join(roots)+', Bool.and_true]\n\ntheorem dcube_cycles : SmallSupportsAreCycles dcubeE := checkB_sound _ dcube_checkB\nend TailFloor\n#print axioms TailFloor.dcube_cycles\n'
open(sys.argv[2] if len(sys.argv)>2 else 'TailFloorDoubleCube.gen.lean','w').write(hdr+body+top)
print(n[0], 'decls')
