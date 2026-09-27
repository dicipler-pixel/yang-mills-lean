#!/usr/bin/env python3
"""Exact budget in LOCAL_WINDOW_AND_GAP_TRANSFER.md, no eigensolver or network.

A passing budget controls truncation error under that theorem's hypotheses;
it does not assert a positive gap for the finite compression. The physical
normalization alpha and lambda is explicit. Run --help or run with no arguments.
"""
from __future__ import annotations
import argparse,json,math
from fractions import Fraction as F
from pathlib import Path


def casimir_shell(s: int) -> F:
    if isinstance(s,bool) or not isinstance(s,int) or s<0:
        raise ValueError('Shell must be a nonnegative integer')
    return F(s*s-(s*s)//4+3*s,3)


def link_dimension(n: int) -> int:
    if n<0:raise ValueError('Negative cutoff')
    return sum(((p+1)*(q+1)*(p+q+2)//2)**2
               for p in range(n+1) for q in range(n+1-p))


def epsilons(alpha: F, incident: F, omega: F, n: int) -> list[F]:
    if alpha<=0 or incident<0 or omega<=0 or n<0:
        raise ValueError('Require alpha>0, incident>=0, omega>0, N>=0')
    values=[F(1)] # entry 0 means epsilon_{-1}
    for k in range(n+1):
        delta=alpha*casimir_shell(k+1)-3*incident-omega
        values.append(min(F(1),F(9,4)*incident*values[-1]/delta) if delta>0 else F(1))
    return values


def budget(classes: list[tuple[int,F,F,int]],omega: F) -> dict:
    """Classes (multiplicity, alpha_e, incident coupling sum Lambda_e, N_e).

    Counts describe actual links. Incident sums must be justified from the
    supplied graph; this arithmetic function cannot verify a graph it is not given.
    """
    if omega<=0 or not classes:raise ValueError('Positive window and link classes required')
    s=k=F(0);details=[]
    for count,alpha,incident,n in classes:
        if isinstance(count,bool) or not isinstance(count,int) or count<1:
            raise ValueError('Multiplicity must be a positive integer')
        es=epsilons(alpha,incident,omega,n);previous,current=es[-2:]
        s+=count*current*current;k+=F(9,4)*count*incident*previous*current
        details.append(dict(count=count,alpha=str(alpha),incident_sum=str(incident),N=n,
                       epsilon=str(current),previous_epsilon=str(previous),
                       one_link_dimension=link_dimension(n)))
    error=(omega*s+k)/(1-s) if s<1 else None
    return dict(window=str(omega),classes=details,S=str(s),K=str(k),
                projection_injective=s<1,error=None if error is None else str(error),
                error_display=None if error is None else float(error),
                finite_compression_gap_required=True,continuum_claim=False)


def cubic_budget(L: int,alpha: F,lam: F,omega: F,n: int) -> dict:
    if isinstance(L,bool) or not isinstance(L,int) or L<3:
        raise ValueError('This incidence formula assumes periodic cubic side L>=3')
    if lam<0:raise ValueError('Negative plaquette coupling')
    out=budget([(3*L**3,alpha,4*lam,n)],omega)
    out.update(side=L,links=3*L**3,plaquettes=3*L**3,lambda_=str(lam))
    return out


def find_cutoff(L: int,alpha: F,lam: F,omega: F,tolerance: F,max_n: int=1000) -> dict:
    if tolerance<=0 or max_n<0:raise ValueError('Positive error budget and nonnegative search limit required')
    for n in range(max_n+1):
        out=cubic_budget(L,alpha,lam,omega,n)
        if out['error'] is not None and F(out['error'])<=tolerance:
            out.update(first_passing_N=n,tolerance=str(tolerance),budget_passed=True)
            return out
    raise ArithmeticError('No passing cutoff in the declared finite range')


def self_test() -> dict:
    count=0
    def check(b):
        nonlocal count
        if not b:raise AssertionError('Exact budget control failed')
        count+=1
    for s in range(101):
        actual=min(F(p*p+q*q+p*q+3*p+3*q,3) for p in range(s+1) for q in [s-p])
        check(actual==casimir_shell(s))
        check(casimir_shell(s+1)>casimir_shell(s))
    for k in range(51):
        check(casimir_shell(2*k)==k*k+2*k)
        check(casimir_shell(2*k+1)==k*k+3*k+F(4,3))
    check(link_dimension(0)==1);check(link_dimension(1)==19)
    for L in [3,4,10,100]:
        r=find_cutoff(L,F(1),F(1),F(1),F(1,10))
        n=r['first_passing_N'];check(F(r['error'])<=F(1,10))
        if n:
            old=cubic_budget(L,F(1),F(1),F(1),n-1)
            check(old['error'] is None or F(old['error'])>F(1,10))
    r=cubic_budget(3,F(1),F(0),F(1),0)
    check(F(r['S'])==0 and F(r['error'])==0)
    refused=0
    bad=[lambda:casimir_shell(-1),lambda:epsilons(F(0),F(1),F(1),1),
         lambda:epsilons(F(1),F(-1),F(1),1),
         lambda:cubic_budget(2,F(1),F(1),F(1),1),
         lambda:find_cutoff(3,F(1),F(1),F(1),F(0)),
         lambda:budget([(0,F(1),F(1),1)],F(1))]
    for fn in bad:
        try:fn()
        except ValueError:refused+=1
    check(refused==len(bad))
    return dict(exact_checks=count,rejected_invalid_inputs=refused)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--side',type=int)
    ap.add_argument('--alpha',type=F,default=F(1));ap.add_argument('--coupling',type=F,default=F(1))
    ap.add_argument('--window',type=F,default=F(1));ap.add_argument('--error',type=F,default=F(1,10))
    ap.add_argument('--out',type=Path,default=Path('local_window_budgets.json'))
    args=ap.parse_args();controls=self_test()
    parameters=[(args.side,args.coupling)] if args.side is not None else [
               (L,lam) for lam in map(F,['0','1/10','1','10','100']) for L in [3,10,100]]
    rows=[find_cutoff(L,args.alpha,lam,args.window,args.error) for L,lam in parameters]
    payload=dict(controls=controls,budgets=rows,large_lattices_simulated=False,
                 meaning='Exact sufficient truncation budgets, not finite-compression gap estimates')
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(payload,indent=2)+'\n')
    print(controls)
    for r in rows:
        print('L',r['side'],'links',r['links'],'lambda',r['lambda_'],'N',r['first_passing_N'],
              'error <=',r['error_display'],'one-link dimension',r['classes'][0]['one_link_dimension'])
    print('Output',args.out)

if __name__=='__main__':main()
