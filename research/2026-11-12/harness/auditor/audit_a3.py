# SCRIPT: AUDIT_A3
# Independent exact recomputation of the even-split plaquette coefficients
# c_p = sum over links e of p of 1/(number of plaquettes containing e).
# No repo code is used. Standard library only.
import sys
from fractions import Fraction as F
from collections import defaultdict

def grid(nx, ny, nz):
    V = [(x, y, z) for x in range(nx) for y in range(ny) for z in range(nz)]
    Vs = set(V)
    E = set(); P = []
    dirs = ((1, 0, 0), (0, 1, 0), (0, 0, 1))
    add = lambda v, d: (v[0] + d[0], v[1] + d[1], v[2] + d[2])
    for v in V:
        for d in dirs:
            if add(v, d) in Vs:
                E.add((v, add(v, d)))
        for i in range(3):
            for j in range(i + 1, 3):
                a, b, c = add(v, dirs[i]), add(v, dirs[j]), add(add(v, dirs[i]), dirs[j])
                if a in Vs and b in Vs and c in Vs:
                    P.append(((v, a), (v, b), (a, c), (b, c)))
    return sorted(E), P
def corner():
    # cube without the vertex (1,1,1): the three faces through (0,0,0)
    E, P = grid(2, 2, 2)
    bad = (1, 1, 1)
    E = [e for e in E if bad not in e]
    P = [p for p in P if all(bad not in e for e in p)]
    return E, P

def coeffs(E, P):
    Es = set(E)
    r = defaultdict(int)
    for p in P:
        assert len(set(p)) == 4
        for e in p:
            assert e in Es
            r[e] += 1
    assert all(r[e] >= 1 for e in E), 'a link lies on no plaquette'
    return [sum(F(1, r[e]) for e in p) for p in P], r

CASES = [
    ('two squares', grid(3, 2, 1), 7, [F(7, 2)] * 2),
    ('three-square strip', grid(4, 2, 1), 10, [F(7, 2), F(3), F(7, 2)]),
    ('three-face corner', corner(), 9, [F(3)] * 3),
    ('cube', grid(2, 2, 2), 12, [F(2)] * 6),
    ('two adjacent cubes', grid(3, 2, 2), 20, None),
]
problems = []
for name, (E, P), nl, claim in CASES:
    c, r = coeffs(E, P)
    assert len(E) == nl
    tot = sum(c)
    print('%-20s links %2d faces %2d  c_p = %s  sum = %s  average = %s' %
          (name, len(E), len(P), [str(x) for x in c], tot, tot / len(P)))
    print('%-20s plaquettes-per-link histogram: %s' % ('', dict(sorted((k, list(r.values()).count(k)) for k in set(r.values())))))
    if tot != len(E):
        problems.append('%s: coefficients sum to %s, not the link count' % (name, tot))
    if claim is not None:
        if sorted(c) != sorted(claim):
            problems.append('%s: %s differs from claimed %s' % (name, c, claim))
        if name == 'three-square strip':
            # the middle face is the one with two shared links
            mid = [x for p, x in zip(P, c) if sum(1 for e in p if r[e] == 2) == 2]
            if mid != [F(3)]:
                problems.append('strip: middle coefficient %s' % mid)
    else:
        if len(P) != 11 or tot / len(P) != F(20, 11):
            problems.append('two cubes: average %s over %d faces, claimed 20/11 over 11' % (tot / len(P), len(P)))
if problems:
    print('RESULT A3: KILLED — ' + ' | '.join(problems)); sys.exit(1)
print('RESULT A3: SURVIVES')
