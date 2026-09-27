#!/usr/bin/env python3
"""Exact finite/local checks for the hypersurface audit; no quantum YM simulation."""
from pathlib import Path
from itertools import permutations
import json
import sympy as s

checks = []
def check(name, statement):
    assert bool(statement), name
    checks.append(name)
def zero(M):
    return all(s.simplify(v) == 0 for v in M)
def comm(A,B):
    return A*B-B*A

I=s.I
pauli=[s.Matrix([[0,1],[1,0]]), s.Matrix([[0,-I],[I,0]]), s.diag(1,-1)]
X,Y,Z=[I*p for p in pauli]
a,b=s.symbols('a b', real=True)
ex=lambda G,t:s.cos(t)*s.eye(2)+s.sin(t)*G
W=ex(Y,-b/2)*ex(X,a/2)*ex(Y,b/2)*ex(X,-a/2)
trace_expected=2-4*s.sin(a/2)**2*s.sin(b/2)**2
check('exact_SU2_rectangle_trace', s.trigsimp(s.trace(W)-trace_expected)==0)
check('embedded_SU3_nonconstant_trace', s.simplify(s.diff(trace_expected,a)+2*s.sin(a)*s.sin(b/2)**2)==0)
check('graph_curvature_nonzero', comm(X,Y)==-2*Z)

# Graded trace identity in components for fully generic 2x2 matrix coefficients.
T=[s.Matrix(2,2,s.symbols('t%d_0:4'%k)) for k in range(4)]
def parity(p):
    return (-1)**sum(p[i]>p[j] for i in range(4) for j in range(i+1,4))
alternating_trace=sum(parity(p)*s.trace(T[p[0]]*T[p[1]]*T[p[2]]*T[p[3]]) for p in permutations(range(4)))
check('generic_2x2_trace_theta_four_zero',s.expand(alternating_trace)==0)

# Matrix trace logarithm response: actual nonzero S-odd tangent, no linear term.
d=s.symbols('d',real=True)
eigs=[s.Rational(1,4)+d,s.Rational(3,4)+d,
      s.Rational(1,3)-s.Rational(32,27)*d,s.Rational(2,3)-s.Rational(32,27)*d]
f=sum(s.log(1-v)-s.log(v) for v in eigs)
fp=s.simplify(s.diff(f,d).subs(d,0))
fppp=s.simplify(s.diff(f,d,3).subs(d,0))
check('Sodd_nonlinear_response_first_derivative_zero',fp==0)
check('Sodd_nonlinear_response_cubic_nonzero',fppp!=0)
check('particle_hole_pair_covariance',all(s.simplify(eigs[i].subs(d,-d)-(1-eigs[j]))==0 for i,j in [(0,1),(1,0),(2,3),(3,2)]))

# Quaternionic weighted-frame repair, standard orientation dx1 dx2 dx3 dx4.
xs=s.symbols('x1:5',real=True)
rho=s.symbols('rho',positive=True)
r2=sum(x*x for x in xs)
D=rho**2+r2
q=xs[3]*s.eye(2)+sum((xs[k]*I*pauli[k] for k in range(3)),s.zeros(2))
check('quaternion_norm',zero(q.H*q-r2*s.eye(2)))
N=s.Matrix.vstack(rho*s.eye(2),q)
check('frame_numerator_orthonormality',zero(N.H*N-D*s.eye(2)))
A=[(q.H*q.diff(x)-x*s.eye(2))/D for x in xs]
for k in range(4):
    check(f'instanton_A{k+1}_su2',s.simplify(s.trace(A[k]))==0 and zero(A[k].H+A[k]))
F={}
for mu in range(4):
    for nu in range(mu+1,4):
        F[mu,nu]=(A[nu].diff(xs[mu])-A[mu].diff(xs[nu])+comm(A[mu],A[nu])).applyfunc(s.simplify)
        expected=(rho**2/D**2)*(q.diff(xs[mu]).H*q.diff(xs[nu])-q.diff(xs[nu]).H*q.diff(xs[mu]))
        check(f'instanton_curvature_{mu+1}{nu+1}',zero(F[mu,nu]-expected))
check('anti_self_dual_12_34',zero(F[0,1]+F[2,3]))
check('anti_self_dual_13_24',zero(F[0,2]-F[1,3]))
check('anti_self_dual_14_23',zero(F[0,3]+F[1,2]))
density=s.factor(2*s.trace(F[0,1]*F[2,3]-F[0,2]*F[1,3]+F[0,3]*F[1,2]))
check('pontryagin_density',s.simplify(density-48*rho**4/D**4)==0)
r=s.symbols('r',positive=True)
integral=s.integrate(2*s.pi**2*r**3*48*rho**4/(r*r+rho*rho)**4,(r,0,s.oo))
check('charge_integral',s.simplify(integral-8*s.pi**2)==0)

result={'kind':'exact symbolic finite/local checks', 'sympy_version':s.__version__,
        'assertions':len(checks),'passed':checks,
        'Sodd_cubic_derivative':str(fppp),
        'Tr_F_wedge_F_density':str(density),
        'integral_Tr_F_wedge_F':str(integral),
        'charge_convention':'nu = -integral Tr(F wedge F)/(8 pi^2)',
        'charge':-1,
        'scope':'No continuum quantum construction, mass-gap proof, or fresh Lean certificate.'}
Path(__file__).with_name('holonomy_results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
