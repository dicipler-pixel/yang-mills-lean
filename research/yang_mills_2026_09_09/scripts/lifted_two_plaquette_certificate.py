#!/usr/bin/env python3
"""Recheck complete-tail two-plaquette certificates with local energy floors.

Run with Python 3 standard library only:
    python -S lifted_two_plaquette_certificate.py --out lifted_results.json

Input targets are untrusted proposals. Recompute every inner and outer pivot.
The allocation/theta-graph/Schur operator proofs are separate written arguments.
This program does not formalize Haar integration or infinite-dimensional analysis
in Lean. See proofs/LOCAL_ENERGY_FLOORS.md and proofs/TWO_PLAQUETTES.md.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from pathlib import Path
import json
import time
import two_plaquette_certificate as tp
import su3_character_certificate as su


def certify_row(target: dict) -> dict:
    lam,r,z,s=(F(target[k]) for k in ('lambda','r','z','s'))
    n=target['N']
    if not isinstance(n,int) or isinstance(n,bool) or n<1:
        raise ValueError('N must be a positive integer')
    if lam<0 or not 0<s<1:
        raise ValueError('Require lambda>=0 and 0<s<1')
    kappa=F(7,2)*(1-s)
    if F(target['kappa'])!=kappa:
        raise ValueError('The shared-edge electric allocation is incorrect')
    t=F(target['single_floor'])
    if not t<kappa*su.tail_floor(n):
        raise ValueError('Single-loop test energy reaches its analytic tail floor')
    negatives,pivots=su.interval_inertia(n,lam/kappa,t/kappa,schur=True)
    if negatives!=0 or any(lo<=0 for lo,hi in pivots):
        raise ArithmeticError('The proposed local ground lower bound is not certified')
    d=s*tp.TAIL+2*t
    if F(target['d'])!=d:
        raise ValueError('Tail lower bound must be derived, not supplied freely')
    result=tp.certify(lam,r,z,d)
    result.update(electric_retention=str(s),local_kappa=str(kappa),
                  local_ground_floor=str(t),local_N=n,
                  local_inertia_negatives=negatives,
                  local_pivot_scale=str(su.SCALE),local_pivot_witnesses=pivots,
                  local_floor_proved_by='positive matrix Schur complement and complete one-loop tail',
                  inner_dimension=len(pivots),accepted=True)
    return result


def destruction_controls(good: dict) -> int:
    controls=[]
    for key,val in (('s','1'),('kappa','1'),('d','100'),('single_floor','1000'),
                    ('r',good['z']),('N',0)):
        bad=good.copy();bad[key]=val;controls.append(bad)
    refused=0
    for bad in controls:
        try:certify_row(bad)
        except (ValueError,ArithmeticError):refused+=1
        else:raise AssertionError('A malformed or false certificate was accepted')
    return refused


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--targets',type=Path,default=Path(__file__).with_name('two_plaquette_lifted_targets.json'))
    ap.add_argument('--out',type=Path,default=Path('lifted_two_plaquette_results.json'))
    args=ap.parse_args();started=time.monotonic()
    nc,nr=tp.checks()
    targets=json.loads(args.targets.read_text())
    rows=[certify_row(t) for t in targets]
    refused=destruction_controls(targets[0])
    payload=dict(model='SU(3), two squares sharing one link, seven links, alpha=1',
                 exact_Haar_structural_checks=nc,base_refused_controls=nr,
                 additional_refused_controls=refused,
                 certificates=rows,
                 new_exact_inertia_certificates=4*len(rows),
                 accepted_pivot_signs=sum(r['inner_dimension']+21 for r in rows),
                 infinite_representation_tail_controlled=True,
                 classical_or_decoupled_substitution=False,
                 continuum_mass_gap_claim=False,
                 elapsed_seconds=time.monotonic()-started)
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(payload,indent=2)+'\n')
    print('Haar/structure checks:',nc,'; base refusals:',nr,'; extra refusals:',refused)
    for r in rows:
        print('lambda/alpha',r['lambda_over_alpha'],'d',r['complete_hidden_floor'],
              'gap >=',r['gap_lower'],'=',r['gap_display'])
    print('Accepted:',payload['new_exact_inertia_certificates'],'inertia certificates;',
          payload['accepted_pivot_signs'],'strict pivot signs; elapsed',payload['elapsed_seconds'])
    print('Output:',args.out)

if __name__=='__main__':main()
