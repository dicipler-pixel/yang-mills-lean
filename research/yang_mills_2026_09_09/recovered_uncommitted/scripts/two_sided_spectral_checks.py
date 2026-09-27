#!/usr/bin/env python3
"""Exact two-sided spectral enclosures for the shared-link SU(3) operator.

Standard-library acceptance; --propose uses SciPy only to propose rational
endpoints. Full infinite-tail lower bounds are validated again, not trusted.
"""
from __future__ import annotations
import argparse,json,math
from fractions import Fraction as F
from pathlib import Path
import two_plaquette_19 as ex
import two_plaquette_certificate as tp

ROOT=Path(__file__).resolve().parent

def shifted(a,g,t):
    return [[a[i][j]-t*g[i][j] for j in range(len(g))] for i in range(len(g))]

def accept(base,proposal):
    previous=ex.certify_row(base)
    lam=F(base['lambda']);d=F(base['d']);l=F(proposal['ground_lower']);w=F(proposal['first_upper'])
    if not l<F(base['r']) or not w>F(base['z']) or not l<d:
        raise ValueError('Invalid enclosure order')
    g,a,m=ex.retained(lam)
    km=[[a[i][j]-l*g[i][j]-m[i][j]/(d-l) for j in range(len(g))] for i in range(len(g))]
    n0,p0=tp.exact_inertia(km);n1,p1=tp.exact_inertia(shifted(a,g,w))
    if n0!=0 or n1<2:raise ArithmeticError('Enclosure inertia failed')
    return dict(lambda_over_alpha=str(lam),E0_interval=[str(l),base['r']],
                E1_interval=[base['z'],str(w)],gap_lower=previous['gap_lower'],
                gap_upper=str(w-l),gap_upper_display=float(w-l),
                ground_lower_pivots=list(map(str,p0)),first_upper_pivots=list(map(str,p1)),
                negative_counts=[n0,n1],all_tail_checked=True)

def propose(bases):
    import numpy as np
    from scipy.linalg import eigvalsh
    proposals=[]
    for t in bases:
        lam,d=F(t['lambda']),F(t['d']);g,a,m=ex.retained(lam)
        gn,an,mn=(np.array(x,dtype=float) for x in (g,a,m))
        ev=eigvalsh(an,gn);lo=-1.;hi=min(float(d)-1e-6,ev[0])
        for _ in range(70):
            mid=(lo+hi)/2
            if eigvalsh(an-mid*gn-mn/(float(d)-mid),subset_by_index=[0,0])[0]>0:lo=mid
            else:hi=mid
        p=dict(ground_lower=str(F(math.floor(lo*10**6)-2,10**6)),
               first_upper=str(F(math.ceil(ev[1]*10**6)+2,10**6)))
        accept(t,p);proposals.append(p)
    return proposals

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--propose',action='store_true')
    ap.add_argument('--targets',type=Path,default=ROOT/'two_sided_targets.json')
    ap.add_argument('--out',type=Path,default=Path('two_sided_results.json'))
    args=ap.parse_args();base=json.loads((ROOT/'two_plaquette_19_targets.json').read_text())
    if args.propose:args.targets.write_text(json.dumps(propose(base),indent=2)+'\n')
    targets=json.loads(args.targets.read_text())
    if len(base)!=len(targets):raise ValueError('Different target counts')
    rows=[accept(t,p) for t,p in zip(base,targets)]
    bad=targets[0].copy();bad['ground_lower']=base[0]['r']
    try:accept(base[0],bad)
    except (ValueError,ArithmeticError):refused=1
    else:raise AssertionError('False lower ground bound accepted')
    payload=dict(enclosures=rows,new_inertia_calculations=2*len(rows),
                 new_pivot_signs=38*len(rows),rechecked_base_certificates=len(rows),
                 refused_false_ground_bound=refused,continuum_claim=False)
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(payload,indent=2)+'\n')
    for r in rows:print(r['lambda_over_alpha'],'gap in [',float(F(r['gap_lower'])),',',r['gap_upper_display'],']')
    print('New inertia checks',payload['new_inertia_calculations'],'new pivot signs',payload['new_pivot_signs'])

if __name__=='__main__':main()
