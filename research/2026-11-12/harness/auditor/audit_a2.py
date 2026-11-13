# SCRIPT: AUDIT_A2
# Independent check of the complete C<=8 physical bases and the 28/3 floor on five graphs.
# No repo code is used. Standard library only.
import sys, time
from fractions import Fraction as F
from collections import defaultdict
from itertools import combinations

# ---------- SU(3) tensor multiplicities (Gelfand-Tsetlin weights + Racah-Speiser) ----------
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
    if r in _W:
        return _W[r]
    p, q = r
    out = defaultdict(int)
    for m12 in range(q, p + q + 1):
        for m22 in range(0, q + 1):
            for m11 in range(m22, m12 + 1):
                w1, w2, w3 = m11, m12 + m22 - m11, p + 2 * q - m12 - m22
                out[(w1 - w2, w2 - w3)] += 1
    assert sum(out.values()) == dim(r)
    _W[r] = dict(out)
    return _W[r]
def to_dominant(x, y):
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
    if (b, c) in _T:
        return _T[(b, c)]
    out = defaultdict(int)
    for (m1, m2), mult in weights(b).items():
        res = to_dominant(c[0] + m1 + 1, c[1] + m2 + 1)
        if res:
            s, x, y = res
            out[(x - 1, y - 1)] += s * mult
    out = {k: v for k, v in out.items() if v}
    assert all(v > 0 for v in out.values())
    _T[(b, c)] = out
    return out
_I = {}
def inv_dim(reps):
    # dim Inv(V_r1 (x) ... (x) V_rk)
    key = tuple(sorted(reps))
    if key in _I:
        return _I[key]
    cur = {(0, 0): 1}
    for r in key:
        nxt = defaultdict(int)
        for a, m in cur.items():
            for b, n in tensor(a, r).items():
                nxt[b] += m * n
        cur = nxt
    _I[key] = cur.get((0, 0), 0)
    return _I[key]
def selftest():
    for p in range(5):
        for q in range(5):
            for p2 in range(5):
                for q2 in range(5):
                    t = tensor((p, q), (p2, q2))
                    assert sum(m * dim(a) for a, m in t.items()) == dim((p, q)) * dim((p2, q2))
    assert tensor((1, 0), (1, 0)) == {(2, 0): 1, (0, 1): 1}
    assert tensor((1, 0), (0, 1)) == {(0, 0): 1, (1, 1): 1}
    assert tensor((1, 1), (1, 1)) == {(0, 0): 1, (1, 1): 2, (3, 0): 1, (0, 3): 1, (2, 2): 1}
    assert inv_dim([(1, 0)]) == 0 and inv_dim([(1, 0), (0, 1)]) == 1 and inv_dim([(1, 0), (1, 0)]) == 0
    assert inv_dim([(1, 0)] * 3) == 1 and inv_dim([(1, 1)] * 3) == 2 and inv_dim([(1, 0), (1, 0), (0, 1), (0, 1)]) == 2

# ---------- graphs, built from their descriptions ----------
def grid(nx, ny, nz):
    V = [(x, y, z) for x in range(nx) for y in range(ny) for z in range(nz)]
    idx = {v: i for i, v in enumerate(V)}
    E = set()
    for (x, y, z) in V:
        for d in ((1, 0, 0), (0, 1, 0), (0, 0, 1)):
            w = (x + d[0], y + d[1], z + d[2])
            if w in idx:
                E.add((idx[(x, y, z)], idx[w]))
    return len(V), sorted(E)
def corner():
    # binary labels 0..6, Hamming distance 1 (cube without 111)
    E = [(a, b) for a in range(7) for b in range(a + 1, 7) if bin(a ^ b).count('1') == 1]
    return 7, E
GRAPHS = [
    ('two squares', grid(3, 2, 1), 7, (2, 1), 7),
    ('three-square strip', grid(4, 2, 1), 10, (3, 2), 11),
    ('three-face corner', corner(), 9, (3, 4), 15),
    ('cube', grid(2, 2, 2), 12, (6, 16), 45),
    ('two adjacent cubes', grid(3, 2, 2), 20, (11, 36), 95),
]
def cycles(nv, E, L):
    adj = defaultdict(list)
    for a, b in E:
        adj[a].append(b); adj[b].append(a)
    found = set()
    def go(path):
        if len(path) == L:
            if path[0] in adj[path[-1]]:
                es = frozenset(tuple(sorted((path[i], path[(i + 1) % L]))) for i in range(L))
                found.add(es)
            return
        for w in adj[path[-1]]:
            if w > path[0] and w not in path:
                go(path + [w])
    for s in range(nv):
        go([s])
    return found

# labels: every irrep with Casimir <= 16/3.  An admissible support has >= 4 links (min degree 2 in a
# simple graph), so a link of Casimir x forces total >= x + 3*(4/3); x > 16/3 gives total > 28/3.
LABELS = [r for r in [(p, q) for p in range(4) for q in range(4)] if 0 < cas(r) <= F(16, 3)]
assert sorted(LABELS) == sorted([(1, 0), (0, 1), (1, 1), (2, 0), (0, 2), (2, 1), (1, 2)])
assert min(cas((p, q)) for p in range(8) for q in range(8) if (p, q) not in LABELS and (p, q) != (0, 0)) > F(16, 3)
BOUND = F(28, 3)

_BL = {}
def budget_labellings(k):
    # all k-tuples of nontrivial labels with total Casimir <= BOUND (same set as a filtered full product)
    if k not in _BL:
        out = []
        def go(pre, tot):
            if len(pre) == k:
                out.append(tuple(pre)); return
            for r in LABELS:
                if tot + cas(r) + F(4, 3) * (k - len(pre) - 1) <= BOUND:
                    go(pre + [r], tot + cas(r))
        go([], F(0))
        _BL[k] = out
    return _BL[k]

def audit(name, nv, E, nlinks, ncyc, claimed_dim, deadline):
    assert len(E) == nlinks, (name, len(E))
    c4, c6 = cycles(nv, E, 4), cycles(nv, E, 6)
    ok = True
    notes = []
    print('---', name, ': vertices', nv, 'links', len(E), '4-cycles', len(c4), '6-cycles', len(c6),
          'dimension 1+2*(c4+c6) =', 1 + 2 * (len(c4) + len(c6)))
    if (len(c4), len(c6)) != ncyc:
        ok = False; notes.append('%s: cycle counts %d/%d differ from %d/%d' % ((name, len(c4), len(c6)) + ncyc))
    if 1 + 2 * (len(c4) + len(c6)) != claimed_dim:
        ok = False; notes.append('%s: dimension differs from %d' % (name, claimed_dim))
    shortcycles = c4 | c6
    inc = defaultdict(list)
    for i, (a, b) in enumerate(E):
        inc[a].append((i, +1)); inc[b].append((i, -1))
    energies = defaultdict(int)      # energy -> number of physical states (product of vertex invariant dims)
    labellings = defaultdict(int)    # energy -> number of admissible labellings
    bad = []
    nsupp = 0
    nadm = 0
    complete = True
    for k in range(1, 8):            # 8 links cost at least 32/3 > 28/3
        for S in combinations(range(len(E)), k):
            if time.time() > deadline:
                complete = False
                break
            nsupp += 1
            deg = defaultdict(int)
            for i in S:
                deg[E[i][0]] += 1; deg[E[i][1]] += 1
            if min(deg.values()) < 2:
                continue             # Gauss law: a vertex with one occupied link has no invariant
            nadm += 1
            verts = list(deg)
            for labs in budget_labellings(k):
                e = sum(cas(r) for r in labs)
                lab = dict(zip(S, labs))
                mult = 1
                for v in verts:
                    reps = [lab[i] if sgn > 0 else dual(lab[i]) for (i, sgn) in inc[v] if i in lab]
                    mult *= inv_dim(reps)
                    if mult == 0:
                        break
                if mult == 0:
                    continue
                energies[e] += mult
                labellings[e] += 1
                fundamental_cycle = (frozenset(E[i] for i in S) in shortcycles
                                     and all(r in ((1, 0), (0, 1)) for r in labs) and mult == 1)
                if e <= 8 and not fundamental_cycle:
                    bad.append(('C<=8 but not a fundamental 4/6-cycle', S, labs, e, mult))
                if 8 < e < BOUND:
                    bad.append(('strictly between 8 and 28/3', S, labs, e, mult))
        if not complete:
            break
    print('    edge subsets examined (sizes 1..7):', nsupp, '; with minimum occupied degree >= 2:', nadm,
          '' if complete else ' [STOPPED AT TIME LIMIT, size %d]' % k)
    print('    energy : physical states (admissible labellings), C <= 28/3, constant state added at 0')
    energies[F(0)] += 1; labellings[F(0)] += 1
    for e in sorted(energies):
        print('      %5s : %d (%d)' % (e, energies[e], labellings[e]))
    low = sum(n for e, n in energies.items() if e <= 8)
    print('    physical dimension with C <= 8:', low, ' claimed', claimed_dim)
    if complete and low != claimed_dim:
        ok = False; notes.append('%s: enumerated C<=8 dimension %d, claimed %d' % (name, low, claimed_dim))
    if bad:
        ok = False; notes.append('%s: %d offending labellings, first %s' % (name, len(bad), bad[0]))
    return ok, complete, notes

def main():
    selftest()
    print('SU(3) multiplicity self-test passed; labels used:', LABELS)
    t0 = time.time()
    allok, allcomplete, notes = True, True, []
    for name, (nv, E), nlinks, ncyc, d in GRAPHS:
        ok, complete, n = audit(name, nv, E, nlinks, ncyc, d, t0 + 1200)
        print('    elapsed %.1f s' % (time.time() - t0))
        allok &= ok; allcomplete &= complete; notes += n
    if not allok:
        print('RESULT A2: KILLED — ' + ' | '.join(notes)); sys.exit(1)
    if not allcomplete:
        print('RESULT A2: INCOMPLETE — enumeration hit the time limit with no violation found'); sys.exit(2)
    print('RESULT A2: SURVIVES')
main()
