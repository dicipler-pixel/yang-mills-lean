# SCRIPT: AUDIT_A1
# Independent recomputation of the two-square (theta 1,3,3) electric spectrum.
# No repo code is used. Standard library only.
import sys
from fractions import Fraction as F
from collections import defaultdict

def cas(r):
    p, q = r
    return F(p*p + q*q + p*q + 3*p + 3*q, 3)

def dim(r):
    p, q = r
    return (p + 1) * (q + 1) * (p + q + 2) // 2

def dual(r):
    return (r[1], r[0])

_W = {}
def weights(r):
    # weight multiplicities of irrep (p,q) from Gelfand-Tsetlin patterns
    # top row (p+q, q, 0); weight in Dynkin labels
    if r in _W:
        return _W[r]
    p, q = r
    m13, m23, m33 = p + q, q, 0
    out = defaultdict(int)
    for m12 in range(m23, m13 + 1):
        for m22 in range(m33, m23 + 1):
            for m11 in range(m22, m12 + 1):
                w1 = m11
                w2 = m12 + m22 - m11
                w3 = m13 + m23 + m33 - m12 - m22
                out[(w1 - w2, w2 - w3)] += 1
    assert sum(out.values()) == dim(r), r
    _W[r] = dict(out)
    return _W[r]

def to_dominant(x, y):
    # reflect a rho-shifted weight into the open dominant chamber; return (sign, x, y) or None on a wall
    s = 1
    while True:
        if x == 0 or y == 0:
            return None
        if x < 0:
            x, y, s = -x, x + y, -s
        elif y < 0:
            x, y, s = x + y, -y, -s
        else:
            return s, x, y

_T = {}
def tensor(b, c):
    # Racah-Speiser: decomposition of V_b (x) V_c as dict irrep -> multiplicity
    key = (b, c)
    if key in _T:
        return _T[key]
    out = defaultdict(int)
    for (m1, m2), mult in weights(b).items():
        res = to_dominant(c[0] + m1 + 1, c[1] + m2 + 1)
        if res is None:
            continue
        s, x, y = res
        out[(x - 1, y - 1)] += s * mult
    out = {k: v for k, v in out.items() if v != 0}
    assert all(v > 0 for v in out.values()), (b, c, out)
    _T[key] = out
    return out

def selftest():
    n = 0
    for p in range(7):
        for q in range(7):
            for p2 in range(7):
                for q2 in range(7):
                    b, c = (p, q), (p2, q2)
                    t = tensor(b, c)
                    assert sum(m * dim(a) for a, m in t.items()) == dim(b) * dim(c), (b, c)
                    assert t == tensor(c, b), (b, c)
                    n += 1
    assert tensor((1, 0), (1, 0)) == {(2, 0): 1, (0, 1): 1}
    assert tensor((1, 0), (0, 1)) == {(0, 0): 1, (1, 1): 1}
    assert tensor((1, 1), (1, 1)) == {(0, 0): 1, (1, 1): 2, (3, 0): 1, (0, 3): 1, (2, 2): 1}
    print('self-test: dimension sum and commutativity on', n, 'pairs with p,q<=6; 3x3, 3x3bar, 8x8 correct')

def main():
    selftest()
    EMAX = F(15)
    R = 8
    reps = [(p, q) for p in range(R + 1) for q in range(R + 1)]
    longreps = [r for r in reps if 3 * cas(r) <= EMAX]
    # any irrep with p or q > R has Casimir >= c(R+1,0) which must exceed EMAX for completeness
    assert cas((R + 1, 0)) > EMAX
    levels = defaultdict(list)
    for b in longreps:
        for c in longreps:
            if 3 * cas(b) + 3 * cas(c) > EMAX:
                continue
            for astar, n in tensor(b, c).items():
                a = dual(astar)          # Inv(a (x) b (x) c) = mult of a* in b (x) c
                e = cas(a) + 3 * cas(b) + 3 * cas(c)
                if e <= EMAX:
                    levels[e].append((a, b, c, n))
    print()
    print('energy | new states (sum n^2) | cumulative | labellings (a short; b, c long; n)')
    cum = 0
    table = []
    for e in sorted(levels):
        new = sum(n * n for (_, _, _, n) in levels[e])
        cum += new
        table.append((e, new, cum))
        print(str(e).rjust(6), '|', str(new).rjust(3), '|', str(cum).rjust(4), '|',
              '; '.join('a=%s b=%s c=%s n=%d' % (a, b, c, n) for (a, b, c, n) in sorted(levels[e])))
    claimed = [(F(0), 1), (F(16, 3), 5), (F(8), 7), (F(28, 3), 9), (F(11), 11), (F(34, 3), 13), (F(12), 15), (F(40, 3), 19)]
    mine = [(e, c) for (e, n, c) in table if e <= F(40, 3)]
    problems = []
    if mine != claimed:
        problems.append('table through 40/3 differs: mine %s' % [(str(e), c) for e, c in mine])
    above = sorted(e for e in levels if e > F(40, 3))
    if not above or above[0] != F(43, 3):
        problems.append('next level after 40/3 is %s, not 43/3' % (above[0] if above else None))
    maxn = max(n for e in levels if e <= F(40, 3) for (_, _, _, n) in levels[e])
    print()
    print('largest intertwiner multiplicity through 40/3:', maxn)
    print('next level above 40/3:', above[0], 'with', sum(n * n for (_, _, _, n) in levels[above[0]]), 'states')
    if problems:
        print('RESULT A1: KILLED — ' + ' | '.join(problems))
        sys.exit(1)
    print('RESULT A1: SURVIVES')

main()
