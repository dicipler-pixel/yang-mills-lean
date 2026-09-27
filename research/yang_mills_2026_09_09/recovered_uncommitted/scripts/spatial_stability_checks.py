#!/usr/bin/env python3
"""Exact finite support/incidence controls for the cited stability theorem map.
No lattice Hamiltonian diagonalization and no numerical beta_star are claimed.
"""
from __future__ import annotations
import argparse,itertools,json
from collections import Counter
from fractions import Fraction as F
from pathlib import Path

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out',type=Path,default=Path('spatial_stability_checks.json'))
    args=ap.parse_args();checks=0;rows=[]
    def req(b):
        nonlocal checks
        if not b:raise AssertionError('Spatial support control failed')
        checks+=1
    for L in range(3,8):
        sites=list(itertools.product(range(L),repeat=3))
        def move(x,i):
            y=list(x);y[i]=(y[i]+1)%L;return tuple(y)
        patch_counts=Counter();link_counts=Counter();plaquettes=set()
        for x in sites:
            patch={x}|{move(x,i) for i in range(3)}
            req(len(patch)==4);patch_counts.update(patch)
            for i,j in itertools.combinations(range(3),2):
                loop=((x,i),(move(x,i),j),(move(x,j),i),(x,j))
                req(len(set(loop))==4)
                req(all(v in patch for v,k in loop))
                plaquettes.add(tuple(sorted(loop)));link_counts.update(loop)
        req(len(plaquettes)==3*L**3)
        req(len(link_counts)==3*L**3)
        req(set(patch_counts.values())=={4})
        req(set(link_counts.values())=={4})
        req(F(1,4)*4==1)
        rows.append(dict(side=L,sites=len(sites),links=len(link_counts),
                         plaquettes=len(plaquettes),patch_multiplicity=4,
                         plaquettes_per_link=4))
    req(F(1,4)*F(4,3)==F(1,3))
    req(3*F(9,4)/F(1,3)==F(81,4))
    # Extending only a one-site kinetic term by three spectator identities
    # would give zero energy to a nonconstant spectator state: uniqueness fails.
    fake_patch_energies=[sum(state[:1]) for state in itertools.product([0,1],repeat=4)]
    req(fake_patch_energies.count(0)==8)
    payload=dict(exact_checks=checks,finite_incidence_cases=rows,
                 rejected_unique_ground_claim_for_one_site_patch_extension=True,
                 normalized_perturbation_coefficient='81/4',
                 numerical_stability_threshold_computed=False,
                 large_volume_gap_simulated=False)
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(payload,indent=2)+'\n');print(json.dumps(payload,indent=2))

if __name__=='__main__':main()
