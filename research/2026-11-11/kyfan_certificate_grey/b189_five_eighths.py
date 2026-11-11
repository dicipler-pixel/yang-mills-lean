#!/usr/bin/env python3
"""B189 constant: why c = 5/8 in  gap(kappa=1, mu) = 2 sqrt(mu) - c + O(mu^-1/2)  for one SU(3) plaquette (Grey).

H = C2 + mu (3 - Re chi_(1,0)) on class functions of SU(3).  (gap(kappa,lam) = kappa G(lam/kappa), so this is B189's c.)

Step 1 (exact, checked below): Weyl reduction.  With delta = Weyl denominator on the maximal torus
  (angles phi_1+phi_2+phi_3 = 0), delta*chi_(p,q) = sum_w sgn(w) exp(i<k,phi>), k = (p+q+2, q+1, 0), and
  C2(p,q) = |k_perp|^2 / 2 - 1.   So  H  ==  -(1/2) Laplace_plane - 1 + mu * sum_j (1 - cos phi_j)
  acting on Weyl-ANTISYMMETRIC functions on the torus.  No curvature term remains (it is the constant -1).
Step 2: harmonic part -(1/2)Lap + (mu/2)|phi|^2, omega = sqrt(mu).  Antisymmetric (S3-sign) states:
  level 4w:  psi0 = D(phi) e^{-w r^2/2},           D = (phi1-phi2)(phi2-phi3)(phi1-phi3)   (r^3 cos 3theta type)
  level 6w:  psi1 = D(phi) (4 - w r^2) e^{-w r^2/2}  (Laguerre L_1^3; the only sign-rep state at that level)
  -> leading gap 2w = 2 sqrt(mu).
Step 3: first anharmonic term  mu*sum(1-cos) - (mu/2)|phi|^2 = -(mu/24) sum phi_j^4 + O(mu phi^6).
  phi ~ mu^-1/4, so this is O(1); the phi^6 term and 2nd order are O(mu^-1/2).
  c = (mu/24) (<sum phi^4>_1 - <sum phi^4>_0)   computed exactly below  ->  5/8.
"""
import sympy as sp
from fractions import Fraction as F
import itertools

# ---- Step 1: exact check of C2(p,q) = |k_perp|^2/2 - 1 and of the neighbour rule as torus multiplication
def c2(p, q): return F(p*p + q*q + p*q + 3*p + 3*q, 3)
for p in range(30):
    for q in range(30):
        k = (p+q+2, q+1, 0); s = sum(k)
        assert c2(p, q) == F(sum(x*x for x in k) - F(s*s, 3)) / 2 - 1
print('Step 1: C2(p,q) = |k_perp|^2/2 - |rho|^2 with |rho|^2 = 1, checked for p,q < 30')
# Re chi_(1,0) = sum_j cos phi_j on the torus: multiplying delta*chi by sum_j e^{+-i phi_j} shifts k by unit vectors;
# this is exactly the six-neighbour rule of the character basis (Pieri).  Spot-check numerically on random angles:
import cmath, random
def chi(p, q, z):
    e = (p+q+2, q+1, 0)
    det = lambda E: sum(sgn * z[a]**E[0]*z[b]**E[1]*z[c]**E[2] for (a, b, c), sgn in
                        (((0,1,2),1),((1,2,0),1),((2,0,1),1),((1,0,2),-1),((0,2,1),-1),((2,1,0),-1)))
    return det(e) / det((2, 1, 0))
rng = random.Random(1)
for _ in range(20):
    a, b = rng.uniform(-3, 3), rng.uniform(-3, 3); z = [cmath.exp(1j*a), cmath.exp(1j*b), cmath.exp(-1j*(a+b))]
    for p, q in ((0,0),(1,0),(2,1),(3,3)):
        lhs = sum(z).real * 2 * chi(p, q, z)   # 2 Re chi_(1,0) chi_(p,q) = (chi_10 + chi_01) chi_pq
        rhs = sum(chi(a_, b_, z) for a_, b_ in ((p+1,q),(p-1,q+1),(p,q-1),(p,q+1),(p+1,q-1),(p-1,q)) if a_ >= 0 and b_ >= 0)
        assert abs(lhs - rhs) < 1e-9
print('Step 1: 2 Re(tr U) chi_pq = sum of six neighbours, checked on random torus points')

# ---- Steps 2-3: exact Gaussian integrals in the plane sum(phi)=0
x, y, w = sp.symbols('x y omega', positive=True)
e1 = sp.Matrix([1, -1, 0]) / sp.sqrt(2); e2 = sp.Matrix([1, 1, -2]) / sp.sqrt(6)
ph = x*e1 + y*e2
r2 = sp.expand(x**2 + y**2)
assert sp.simplify(sum(t**2 for t in ph) - r2) == 0
D = sp.expand((ph[0]-ph[1])*(ph[1]-ph[2])*(ph[0]-ph[2]))
g = sp.exp(-w*r2/2)
lap = lambda f: sp.diff(f, x, 2) + sp.diff(f, y, 2)
Hh = lambda f: -lap(f)/2 + w**2*r2*f/2
psi0 = D*g; psi1 = D*(4 - w*r2)*g
assert sp.simplify(Hh(psi0) - 4*w*psi0) == 0 and sp.simplify(Hh(psi1) - 6*w*psi1) == 0
# antisymmetry under the transposition phi1<->phi2  (x -> -x, y -> y)
assert sp.simplify(D.subs(x, -x) + D) == 0
def ev(f, op):
    num = sp.integrate(sp.integrate(sp.expand(f*f*op), (x, -sp.oo, sp.oo)), (y, -sp.oo, sp.oo))
    den = sp.integrate(sp.integrate(sp.expand(f*f), (x, -sp.oo, sp.oo)), (y, -sp.oo, sp.oo))
    return sp.simplify(num/den)
assert ev(psi0, psi1/psi0 if False else 1) == 1
ov = sp.integrate(sp.integrate(sp.expand(psi0*psi1), (x, -sp.oo, sp.oo)), (y, -sp.oo, sp.oo))
assert sp.simplify(ov) == 0
P4 = sp.expand(sum(t**4 for t in ph))
m0, m1 = ev(psi0, P4), ev(psi1, P4)
c = sp.simplify(w**2/24*(m1 - m0))
print('Step 2: H_harm psi0 = 4w psi0, H_harm psi1 = 6w psi1, <psi0,psi1> = 0, sign rep checked')
print('Step 3: <sum phi^4>_0 =', m0, '  <sum phi^4>_1 =', m1)
print('        c = (mu/24)(<.>_1 - <.>_0) =', c)
assert c == sp.Rational(5, 8)
# per-level first-order shifts (for the record): E0 = 4w - 1 - (mu/24)<.>_0 + ..., E1 = 6w - 1 - (mu/24)<.>_1 + ...
print('        E0 = 4 sqrt(mu) - 1 -', sp.simplify(w**2*m0/24), '+ O(mu^-1/2);  E1 = 6 sqrt(mu) - 1 -',
      sp.simplify(w**2*m1/24), '+ O(mu^-1/2)')

# ---- Control (must fail): the same computation with the U(1)-style or wrong quartic weight does not give 5/8
c_wrong = sp.simplify(w**2/12*(m1 - m0))
assert c_wrong != sp.Rational(5, 8)
print('Control: doubling the quartic coefficient gives c =', c_wrong, '!= 5/8 (rejected)')

# ---- Numerical cross-check against the exact operator (float; not part of the proof)
import numpy as np
def hf(n, mu):
    ss = [(p, s-p) for s in range(n+1) for p in range(s+1)]; ix = {s: i for i, s in enumerate(ss)}
    h = np.zeros((len(ss),)*2)
    for i, (p, q) in enumerate(ss):
        h[i, i] = float(c2(p, q)) + 3*mu
        for t in ((p+1,q),(p-1,q+1),(p,q-1),(p,q+1),(p+1,q-1),(p-1,q)):
            j = ix.get(t)
            if j is not None: h[i, j] = -mu/2
    return h
print('Numerics: mu, E0 - (4sqrt(mu) - 1 - %s),  c(mu) = 2sqrt(mu) - gap,  sqrt(mu)*(c(mu) - 5/8)' % sp.simplify(w**2*m0/24))
for mu in (64, 256, 1024, 4096):
    n = int(12*mu**0.25) + 40
    e = np.linalg.eigvalsh(hf(n, mu))[:2]; cm = 2*np.sqrt(mu) - (e[1]-e[0])
    print(f'  mu={mu:5d}  N={n:3d}  E0 resid {e[0]-(4*np.sqrt(mu)-1-float(w**2*m0/24)):+.5f}   c={cm:.6f}   '
          f'sqrt(mu)(c-5/8)={np.sqrt(mu)*(cm-0.625):+.4f}')
