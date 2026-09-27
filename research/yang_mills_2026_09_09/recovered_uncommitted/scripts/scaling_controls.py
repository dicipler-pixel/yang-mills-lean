#!/usr/bin/env python3
"""Exact controls for SCALING_AND_OBSTRUCTIONS.md; no large-lattice simulation."""
from __future__ import annotations
import argparse,json
from fractions import Fraction as F
from pathlib import Path
from local_window_budget import budget,casimir_shell,link_dimension


def dimension_formula(n: int) -> int:
    if isinstance(n,bool) or not isinstance(n,int) or n<0:raise ValueError('Nonnegative integer cutoff required')
    numerator=(n+1)*(n+2)**2*(n+3)**2*(n+4)*(3*n*n+15*n+20)
    value,remainder=divmod(numerator,2880)
    if remainder:raise ArithmeticError('Dimension formula lost integrality')
    return value


def dyadic_budget(h: int,R: int=1) -> dict:
    if isinstance(h,bool) or not isinstance(h,int) or h<2:raise ValueError('Integer h>=2 required')
    if isinstance(R,bool) or not isinstance(R,int) or R<1:raise ValueError('Positive integer R required')
    alpha=F(2**h,h);lam=F(h*2**h);n=16*h;M=3*R**3*2**(3*h)
    result=budget([(M,alpha,4*lam,n)],F(1))
    sb=F(27,16)*R**3*F(531441,2097152)**h
    kb=F(81,4)*R**3*h*F(531441,1048576)**h
    if F(result['S'])>sb or F(result['K'])>kb:raise AssertionError('Envelope violation')
    result.update(h=h,R=R,a=str(F(1,2**h)),lambda_=str(lam),links=M,
                  analytic_S_envelope=str(sb),analytic_K_envelope=str(kb),
                  analytic_error_envelope=str((sb+kb)/(1-sb)) if sb<1 else None,
                  assumed_Yang_Mills_renormalization=False,large_lattice_simulated=False)
    return result


def controls() -> dict:
    n=0
    def check(b):
        nonlocal n
        if not b:raise AssertionError('Exact scale control failed')
        n+=1
    for N in range(81):
        check(dimension_formula(N)==link_dimension(N))
        previous=dimension_formula(N-1) if N else 0
        check(dimension_formula(N)-previous==((N+2)**7-(N+2)**3)//120)
    # Exact polynomial identities at rational points are implementation controls;
    # the all-N proof is by polynomial expansion and telescoping in the note.
    for h in range(2,31):
        alpha=F(2**h,h);lam=F(h*2**h)
        for k in range(10*h,16*h+1):
            delta=alpha*casimir_shell(k+1)-12*lam-1
            check(casimir_shell(k+1)>=F(k*k,4))
            check(delta>=12*h*2**h)
            check(9*lam/delta<=F(3,4))
    check(F(531441,2097152)<1)
    check(F(531441,1048576)<F(3,4))
    check(F(9,4)**2>5 and F(2)**2<5)
    # sqrt5 in (2,9/4), e0>3/8; no floating root is needed.
    check(14*F(3,8)>5)
    for h in range(4,101):check(F(h+1,h)*F(3,4)<=F(15,16))
    # Bare/interacting overlap p<3/4 follows from sqrt5>2.
    check(F(1,2)*(1+F(1,2))==F(3,4))
    refused=0
    for fn in (lambda:dimension_formula(-1),lambda:dyadic_budget(1),lambda:dyadic_budget(2,0)):
        try:fn()
        except ValueError:refused+=1
    check(refused==3)
    return dict(exact_checks=n,invalid_inputs_rejected=refused)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out',type=Path,default=Path('scaling_controls.json'))
    args=ap.parse_args()
    rows=[dyadic_budget(h,R) for R in (1,2,10) for h in (2,3,4,6,8,12,16,20)]
    payload=dict(controls=controls(),budgets=rows,continuum_claim=False,
                 description='Declared trajectory and exact error budgets; no finite-compression gaps computed')
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(payload,indent=2)+'\n')
    print(payload['controls'])
    for row in rows:
        print('R',row['R'],'h',row['h'],'N',row['classes'][0]['N'],
              'error',row['error_display'],'link dimension',row['classes'][0]['one_link_dimension'])
    print('Output',args.out)

if __name__=='__main__':main()
