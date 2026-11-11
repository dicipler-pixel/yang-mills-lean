#!/usr/bin/env python3
"""Ky Fan chord certificate, one SU(3) plaquette, lam = 8, kappa in [1/2, 2]  (Grey, 2026-11-11).

Single entry point.
  python3 kyfan_cert.py            verify certificate.json (Python standard library only; no floats decide anything)
  python3 kyfan_cert.py --generate re-propose certificate.json (NumPy proposes numbers; the verifier then re-checks)
  python3 kyfan_cert.py --controls run the must-fail controls (also run by default after verification)

Model (repo su3_character_certificate / ledger open_tests_05 T2):
  H(kappa) = kappa*C2 + lam*V,  V = 3 - Re chi_(1,0),  on class functions of the plaquette holonomy,
  orthonormal characters chi_(p,q): C2 diagonal (p^2+q^2+pq+3p+3q)/3, V = 3*Id - (1/2)*(six neighbours).
Certificate content (all exact rationals):
  (1) nodes kappa_j: z0_j <= E0(kappa_j), z1_j <= E1(kappa_j)  -- outward-rounded integer-interval LDL inertia of the
      truncated block (p+q <= N) minus a Schur tail bound; Haynsworth + Sylvester.
  (2) trial vectors v_i (finite support, rational): E0(kappa) <= (kappa*<v,C2 v> + lam*<v,V v>)/<v,v> for EVERY kappa
      (variational principle; v lies in the form domain of the full operator).
  (3) Ky Fan: kappa -> E0+E1 is concave (inf over 2-frames of affine functions of kappa), so on a chord [a,b]
      gap(kappa) >= chord(S_lo)(kappa) - 2*min_i q_i(kappa)  (exactly the statement of KyFanChord.chord_gap_lower_inf).
      The right-hand side is convex piecewise linear; its exact minimum over [a,b] is taken over all vertices.
"""
import sys, json, argparse, time, pathlib
from fractions import Fraction as F

HERE = pathlib.Path(__file__).resolve().parent
CERT = HERE / 'certificate.json'
LAM = F(8)

# ------------------------------------------------------------------ model (exact)
def states(n):
    return [(p, s - p) for s in range(n + 1) for p in range(s + 1)]

def nbrs(p, q):
    return [(a, b) for a, b in ((p + 1, q), (p - 1, q + 1), (p, q - 1), (p, q + 1), (p + 1, q - 1), (p - 1, q))
            if a >= 0 and b >= 0]

def c2(p, q):
    return F(p * p + q * q + p * q + 3 * p + 3 * q, 3)

def tail_floor(n):
    """min C2 over p+q >= n+1.  C2 = (s^2 - pq + 3s)/3 >= (3s^2/4 + 3s)/3, increasing in s, so the min sits on level
    n+1; we also check levels n+1..n+40 explicitly."""
    d = min(c2(p, n + 1 - p) for p in range(n + 2))
    for s in range(n + 1, n + 41):
        assert min(c2(p, s - p) for p in range(s + 1)) >= d
        assert F(3 * s * s, 4) / 3 + s >= F(3 * (n + 1) ** 2, 4) / 3 + (n + 1) or s == n + 1
    return d

# ------------------------------------------------------------------ outward interval arithmetic on a 2^-B grid
B = 224
S = 1 << B
def cdiv(a, b):
    return -((-a) // b)
def enc(x):
    x = F(x); return (x.numerator * S // x.denominator, cdiv(x.numerator * S, x.denominator))
def isub(a, b):
    return (a[0] - b[1], a[1] - b[0])
def imulquot(a, b, c):
    """enclosure of (a*b/c) on the grid; a, b, c are grid-scaled intervals, c does not contain 0"""
    assert c[0] > 0 or c[1] < 0
    ps = [x * y for x in a for y in b]
    lo, hi = min(ps), max(ps)
    qs_lo = [x // y for x in (lo, hi) for y in c]
    qs_hi = [cdiv(x, y) for x in (lo, hi) for y in c]
    return (min(qs_lo), max(qs_hi))

def negcount(kap, lam, z, n):
    """Upper bound on #{eigenvalues of H(kap,lam) below z} (multiplicity counted).

    H - z = [[A-z, Bc],[Bc*, D-z]] with A the block p+q<=n, D the tail.  D >= kap*d (C2 diagonal, V >= 0 is a
    multiplication operator, compressions keep V >= 0).  If z < kap*d, Haynsworth: #neg(H-z) = #neg(Schur), and
    Schur = A - z - Bc (D-z)^-1 Bc* >= A - z - Bc Bc*/(kap*d - z) =: K.  So #neg(H-z) <= #neg(K).
    Bc Bc* = (lam^2/4) M with M the boundary overlap matrix (computed here, not assumed).
    #neg(K) is computed by interval LDL: if no pivot interval contains 0, the exact LDL exists with the same signs."""
    ss = states(n); idx = {s: i for i, s in enumerate(ss)}
    d = tail_floor(n); assert z < kap * d, 'shift not below tail floor'
    ent = {}
    for i, (p, q) in enumerate(ss):
        ent[i, i] = kap * c2(p, q) + 3 * lam - z
        for t in nbrs(p, q):
            j = idx.get(t)
            if j is not None and j > i:
                ent[i, j] = -lam / 2
    bnd = [i for i, (p, q) in enumerate(ss) if p + q == n]
    out = {i: {t for t in nbrs(*ss[i]) if t not in idx} for i in bnd}
    corr = lam * lam / (4 * (kap * d - z))
    for a in bnd:
        for b in bnd:
            if b >= a:
                m = len(out[a] & out[b])
                if m:
                    ent[a, b] = ent.get((a, b), F(0)) - corr * m
    size = len(ss); bw = max(j - i for i, j in ent)
    rows = [[(0, 0)] * min(bw + 1, size - i) for i in range(size)]
    for (i, j), v in ent.items():
        rows[i][j - i] = enc(v)
    neg = 0
    for k in range(size):
        pv = rows[k][0]
        if pv[0] <= 0 <= pv[1]:
            raise ArithmeticError('pivot interval contains 0 at %d' % k)
        neg += pv[1] < 0
        rk = rows[k]; end = min(size, k + bw + 1)
        for i in range(k + 1, end):
            a = rk[i - k]
            if a == (0, 0): continue
            ri = rows[i]
            for j in range(i, end):
                b = rk[j - k]
                if b != (0, 0):
                    ri[j - i] = isub(ri[j - i], imulquot(a, b, pv))
    return neg

def quotient(vec):
    """vec: dict (p,q)->Fraction.  Returns exact (<v,v>, <v,C2 v>, <v,V v>) in the full space."""
    n = sum(x * x for x in vec.values())
    c = sum(x * x * c2(*s) for s, x in vec.items())
    off = sum(x * vec.get(t, 0) for s, x in vec.items() for t in nbrs(*s))
    return n, c, 3 * n - off / 2

def line_of(vec, lam=LAM):
    n, c, m = quotient(vec)
    return (c / n, lam * m / n)       # E0(kappa) <= alpha*kappa + beta for all kappa > 0

# ------------------------------------------------------------------ chord evaluation (exact)
def chord_fn(a, b, Sa, Sb, lines):
    def f(x):
        return Sa + (Sb - Sa) * (x - a) / (b - a) - 2 * min(al * x + be for al, be in lines)
    return f

def uniform_min(a, b, Sa, Sb, lines):
    f = chord_fn(a, b, Sa, Sb, lines)
    cand = {a, b}
    for i in range(len(lines)):
        for j in range(i + 1, len(lines)):
            (a1, b1), (a2, b2) = lines[i], lines[j]
            if a1 != a2:
                x = (b2 - b1) / (a1 - a2)
                if a < x < b: cand.add(x)
    return min((f(x), x) for x in cand)

def psd2(Mx):
    (p, q), (_, r) = Mx
    return p >= 0 and r >= 0 and p * r - q * q >= 0

# ------------------------------------------------------------------ verifier
def load(cert):
    vecs = [{(s[0], s[1]): F(c, v['den']) for s, c in zip(v['support'], v['num'])} for v in cert['trial_vectors']]
    return vecs

def verify(cert, log=print):
    N = cert['N']; lam = F(cert['lam']); assert lam == LAM
    vecs = load(cert)
    lines = [line_of(v) for v in vecs]
    for L, claimed in zip(lines, cert['claimed_lines']):
        assert (str(L[0]), str(L[1])) == tuple(claimed), 'claimed Rayleigh line does not match its trial vector'
    Slo = {}
    for nd in cert['nodes']:
        k, z0, z1 = F(nd['kappa']), F(nd['z0']), F(nd['z1'])
        n0 = negcount(k, lam, z0, N); n1 = negcount(k, lam, z1, N)
        assert n0 == 0, ('E0 lower bound not certified', nd)
        assert n1 <= 1, ('E1 lower bound not certified', nd)
        up = min(al * k + be for al, be in lines)
        assert z0 <= up, 'E0 lower bound above a Rayleigh quotient: inconsistent'
        Slo[k] = z0 + z1
        log(f"  node kappa={str(k):>4}: E0 in [{float(z0):.10f}, {float(up):.10f}] (width {float(up-z0):.1e}),"
            f" E1 >= {float(z1):.10f}   [neg counts {n0}, {n1}]")
    res = []
    for pc in cert['pieces']:
        a, b = F(pc['a']), F(pc['b'])
        Ls = [lines[i] for i in pc['lines']]
        mn, at = uniform_min(a, b, Slo[a], Slo[b], Ls)
        assert mn >= F(pc['claimed_min']), ('piece claim too high', pc, float(mn))
        res.append((a, b, mn, at))
        log(f"  piece [{str(a)}, {str(b)}]: gap >= {float(mn):.8f} for every kappa in it (exact min at kappa={str(at)})"
            f"; claimed {pc['claimed_min']}")
    G = min(r[2] for r in res)
    assert G >= F(cert['claimed_uniform']), 'uniform claim too high'
    # E1 upper bound at kappa = 1/2 (2-dim Rayleigh-Ritz) -> gap upper bound, used by the controls
    e1 = cert['E1_upper']
    k = F(e1['kappa']); t = F(e1['t'])
    W = [vecs[i] for i in e1['vectors']]
    def form(u, v, kind):
        if kind == 'G': return sum(x * v.get(s, 0) for s, x in u.items())
        cc = sum(x * v.get(s, 0) * c2(*s) for s, x in u.items())
        vv = 3 * sum(x * v.get(s, 0) for s, x in u.items()) - sum(x * v.get(t_, 0) for s, x in u.items() for t_ in nbrs(*s)) / 2
        return k * cc + lam * vv
    Gm = [[form(u, v, 'G') for v in W] for u in W]; Am = [[form(u, v, 'A') for v in W] for u in W]
    assert psd2([[t * Gm[i][j] - Am[i][j] for j in range(2)] for i in range(2)]) and Gm[0][0] > 0 and \
        Gm[0][0] * Gm[1][1] - Gm[0][1] ** 2 > 0, 'E1 upper bound not certified'
    z0_half = F(next(nd['z0'] for nd in cert['nodes'] if F(nd['kappa']) == k))
    gap_up = t - z0_half
    log(f"  E1(kappa=1/2) <= {float(t):.10f} (2-vector Rayleigh-Ritz), so gap(1/2) <= {float(gap_up):.10f}")
    return dict(G=G, pieces=res, lines=lines, Slo=Slo, gap_up_half=gap_up)

# ------------------------------------------------------------------ controls (each must FAIL)
def controls(cert, out):
    import copy
    N = cert['N']; lam = LAM; ok = []
    def expect_fail(name, fn):
        try:
            fn(); ok.append((name, False)); print('  CONTROL DID NOT FAIL:', name)
        except AssertionError as e:
            ok.append((name, True)); print('  rejected (as required):', name)
    for nd in (cert['nodes'][0], cert['nodes'][-1]):
        k, z0, z1 = F(nd['kappa']), F(nd['z0']), F(nd['z1'])
        expect_fail(f'E0 lower bound +1/1000 at kappa={nd["kappa"]}',
                    lambda: (_ for _ in ()).throw(AssertionError) if negcount(k, lam, z0 + F(1, 1000), N) >= 1 else None)
        expect_fail(f'E1 lower bound +1/1000 at kappa={nd["kappa"]}',
                    lambda: (_ for _ in ()).throw(AssertionError) if negcount(k, lam, z1 + F(1, 1000), N) >= 2 else None)
    # tampered certificate: endpoint z0 raised by 1/1000 must be rejected by the verifier itself
    c2_ = copy.deepcopy(cert); c2_['nodes'][0]['z0'] = str(F(c2_['nodes'][0]['z0']) + F(1, 1000))
    expect_fail('verifier on certificate with endpoint z0(1/2) + 1/1000', lambda: verify(c2_, log=lambda *a: None))
    # E0 upper bound lowered below the Ritz value: claimed line shifted down by 1/1000
    c3 = copy.deepcopy(cert); al, be = c3['claimed_lines'][0]; c3['claimed_lines'][0] = [al, str(F(be) - F(1, 1000))]
    expect_fail('verifier on Rayleigh line lowered by 1/1000', lambda: verify(c3, log=lambda *a: None))
    # ... and mathematically: a lowered E0 upper value u-1/1000 at every node is below the certified E0 lower bound
    def lowered_contradiction():
        for nd in cert['nodes']:
            k = F(nd['kappa']); u = min(a_ * k + b_ for a_, b_ in out['lines'])
            assert not (F(nd['z0']) > u - F(1, 1000)), 'claimed E0 <= u - 1/1000 is refuted by certified E0 >= z0'
    expect_fail('E0 upper bound lowered by 1/1000 at each node (refuted by certified z0)', lowered_contradiction)
    # uniform gap claim raised by 1/1000 is refuted by the certified upper bound on gap(1/2)
    def raised():
        assert out['gap_up_half'] >= out['G'] + F(1, 1000), 'claimed gap >= G+1/1000 contradicts gap(1/2) <= ' + \
            str(float(out['gap_up_half']))
    expect_fail('uniform gap bound raised by 1/1000 (refuted by gap(1/2) upper bound)', raised)
    # claimed piece bound raised by 1/1000 must be rejected by the verifier
    c4 = copy.deepcopy(cert)
    pc = c4['pieces'][0]; mn = next(r[2] for r in out['pieces'] if r[0] == F(pc['a']))
    pc['claimed_min'] = str(mn + F(1, 1000))
    expect_fail('verifier on piece-0 claim raised by 1/1000', lambda: verify(c4, log=lambda *a: None))
    return ok

# ------------------------------------------------------------------ generator (floats only propose)
def generate(N=32, K=6, tang=4, eps=F(1, 10**10)):
    import numpy as np
    def hf(n, kap, lam):
        ss = states(n); ix = {s: i for i, s in enumerate(ss)}; h = np.zeros((len(ss),) * 2)
        for i, (p, q) in enumerate(ss):
            h[i, i] = kap * float(c2(p, q)) + 3 * lam
            for t in nbrs(p, q):
                j = ix.get(t)
                if j is not None: h[i, j] = -lam / 2
        return ss, h
    a0, b0 = F(1, 2), F(2)
    nodes = [a0 + (b0 - a0) * F(i, K) for i in range(K + 1)]
    cert = dict(model='H = kappa*C2 + lam*(3 - Re chi_(1,0)) on class functions of one SU(3) plaquette',
                lam='8', N=N, interval='[1/2, 2]', nodes=[], trial_vectors=[], claimed_lines=[], pieces=[])
    for k in nodes:
        w = np.linalg.eigvalsh(hf(N + 12, float(k), 8.0)[1])
        cert['nodes'].append(dict(kappa=str(k), z0=str(F(w[0]).limit_denominator(10**12) - eps),
                                  z1=str(F(w[1]).limit_denominator(10**12) - eps)))
    tpts = sorted({a + (b - a) * F(i, tang) for a, b in zip(nodes, nodes[1:]) for i in range(tang + 1)})
    den = 10**12
    def addvec(k, which=0):
        ss, h = hf(N, float(k), 8.0); w, V = np.linalg.eigh(h); v = V[:, which] * np.sign(V[0, which] or 1)
        sup = [(s, int(round(x * den))) for s, x in zip(ss, v) if round(x * den)]
        cert['trial_vectors'].append(dict(tuned_at=str(k), level=which, den=den,
                                          support=[list(s) for s, _ in sup], num=[c for _, c in sup]))
        return len(cert['trial_vectors']) - 1
    tix = {k: addvec(k) for k in tpts}
    vecs = load(cert)
    cert['claimed_lines'] = [[str(x) for x in line_of(v)] for v in vecs]
    for a, b in zip(nodes, nodes[1:]):
        li = [tix[k] for k in tpts if a <= k <= b]
        cert['pieces'].append(dict(a=str(a), b=str(b), lines=li, claimed_min='0'))
    # E1 upper at kappa=1/2: Ritz on {ground, first excited}
    i1 = addvec(F(1, 2), 1)
    cert['claimed_lines'] = [[str(x) for x in line_of(v)] for v in load(cert)]
    w = np.linalg.eigvalsh(hf(N + 12, 0.5, 8.0)[1])
    cert['E1_upper'] = dict(kappa='1/2', vectors=[tix[F(1, 2)], i1], t=str(F(w[1]).limit_denominator(10**9) + F(1, 10**8)))
    cert['claimed_uniform'] = '0'
    out = verify(cert, log=lambda *a: None)
    for pc, r in zip(cert['pieces'], out['pieces']):
        pc['claimed_min'] = str(F(int(r[2] * 10**8), 10**8))     # rounded down to 1e-8
    cert['claimed_uniform'] = str(F(int(out['G'] * 10**8), 10**8))
    CERT.write_text(json.dumps(cert, indent=0))
    print('wrote', CERT)

if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--generate', action='store_true')
    ap.add_argument('--N', type=int, default=32)
    a = ap.parse_args()
    t0 = time.time()
    if a.generate:
        generate(N=a.N)
    cert = json.loads(CERT.read_text())
    print(f'Verifying {CERT.name}: lam={cert["lam"]}, kappa in {cert["interval"]}, truncation N={cert["N"]}, '
          f'{len(cert["trial_vectors"])} rational trial vectors, interval grid 2^-{B}')
    out = verify(cert)
    print(f'CERTIFIED: gap(kappa) >= {cert["claimed_uniform"]} (= {float(F(cert["claimed_uniform"])):.8f}) for every '
          f'kappa in [1/2, 2]  (exact min of the bound: {out["G"]} ~ {float(out["G"]):.10f})')
    print(f'  and gap(1/2) <= {float(out["gap_up_half"]):.10f}, so the uniform bound is tight to '
          f'{float(out["gap_up_half"] - out["G"]):.1e}')
    print('Controls (each must be rejected):')
    ok = controls(cert, out)
    assert all(r for _, r in ok), 'a control passed that should have failed'
    print(f'all {len(ok)} controls rejected.  elapsed {time.time()-t0:.1f}s')
