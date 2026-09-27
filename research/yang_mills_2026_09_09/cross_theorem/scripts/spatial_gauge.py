#!/usr/bin/env python3
"""Exact low-electric-energy SU(3) models on declared finite cell graphs.

The complete C<=8 physical basis is proved by support/Gauss-law enumeration in
proofs/SPATIAL_BASES.md. Exact Haar contractions and the original-link Casimir
produce both the full boundary Gram and its resolved electric-energy weights.
No individual omitted representation is substituted by a numerical cutoff.
"""
from __future__ import annotations
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations,product
from pathlib import Path
import argparse,json,time
import gauge_polynomials as gp
import two_plaquette_certificate as old


def canon_cycle(c):
    c=list(c);d=list(reversed(c))
    return min([tuple(c[i:]+c[:i])for i in range(len(c))]+[tuple(d[i:]+d[:i])for i in range(len(d))])

def cycles(vertices,edges):
    adj={v:set()for v in vertices}
    for u,v in edges:adj[u].add(v);adj[v].add(u)
    out=set()
    def extend(path):
        for v in sorted(adj[path[-1]]):
            if v==path[0] and len(path)>2:out.add(canon_cycle(path))
            elif v>path[0] and v not in path:extend(path+[v])
    for s in vertices:extend([s])
    return sorted(out,key=lambda c:(len(c),c))

def model(name):
    if name in ('corner','cube'):
        vs=list(range(7 if name=='corner' else 8));es=[(u,v)for u in vs for v in vs if u<v and(u^v).bit_count()==1]
        label=('Three mutually adjacent faces at an open cubic corner; cube graph minus vertex111' if name=='corner' else 'One full open-boundary elementary cube:12 links,8 vertices,6 plaquettes,5 independent graph cycles')
    elif name=='double_cube':
        coords=list(product(range(3),range(2),range(2)));vs=list(range(len(coords)))
        es=[(u,v)for u in vs for v in vs if u<v and sum(abs(a-b)for a,b in zip(coords[u],coords[v]))==1]
        label='Two adjacent open elementary cubes:12 vertices,20 links,11 distinct plaquettes,9 independent graph cycles'
    elif name in('two','strip'):
        cells=2 if name=='two' else 3;w=cells+1;vs=list(range(2*w));es=[]
        for i in range(cells):es.extend([(i,i+1),(w+i,w+i+1)])
        es +=[(i,w+i)for i in range(w)];label=f'Open strip of{cells} elementary square plaquettes'
    elif name=='vertex_wedge':
        vs=list(range(7));es=[(0,1),(1,2),(2,3),(0,3),(0,4),(4,5),(5,6),(0,6)]
        label='Two edge-disjoint square plaquettes meeting at one vertex; comparison only'
    else:raise ValueError('Unknown declared graph')
    es=sorted(tuple(sorted(e))for e in es);cs=cycles(vs,es);faces=[c for c in cs if len(c)==4]
    tree=[];seen={vs[0]}
    while len(seen)<len(vs):
        nxt=next((e for e in es if(e[0]in seen) !=(e[1]in seen)),None)
        if nxt is None:raise ValueError('Disconnected graph')
        tree.append(es.index(nxt));seen.update(nxt)
    chords=sorted(set(range(len(es)))-set(tree))
    def w(c):return tuple((es.index(tuple(sorted((a,b)))),1 if a<b else -1)for a,b in zip(c,c[1:]+c[:1]))
    basis=[()] ; names=['1'];energies=[F(0)]
    for c in cs:
        if len(c)>6:continue
        ww=w(c);basis.extend([ww,tuple((e,-s)for e,s in reversed(ww))]);names.extend([str(c),str(c)+' conjugate']);energies.extend([F(4,3)*len(c)]*2)
    return dict(name=name,description=label,vertices=vs,edges=es,cycles=cs,faces=faces,tree=tree,chords=chords,
                basis_words=basis,basis_names=names,energies=energies,face_words=[w(c)for c in faces],tail=F(28,3),cutoff=F(8))

def support_check(m):
    """Complete finite enumeration of graph supports with <=6 occupied edges.

    Gauss invariance excludes degree-one supports; every survivor must be one
    simple cycle. Representation-theoretic consequences are a written proof.
    """
    es=m['edges'];survivors=[];tested=0
    for k in range(1,min(6,len(es))+1):
        for inds in combinations(range(len(es)),k):
            tested+=1;deg={}
            for i in inds:
                for v in es[i]:deg[v]=deg.get(v,0)+1
            if min(deg.values())<2:continue
            if any(d!=2 for d in deg.values()):raise AssertionError('Branched small support invalidates basis theorem')
            todo={next(iter(deg))};seen=set()
            while todo:
                v=todo.pop();seen.add(v)
                for i in inds:
                    if v in es[i]:todo.update(set(es[i])-seen)
            if seen!=set(deg):raise AssertionError('Disconnected small support invalidates basis theorem')
            if k not in(4,6):raise AssertionError('Unexpected short cycle')
            survivors.append(list(inds))
    return dict(tested_edge_subsets=tested,all_degree_two_survivors=survivors,cycle_lengths=[len(x)for x in survivors],scope='All supports with at most6 occupied original edges; no degree-one gauge state')

@lru_cache(None)
def calculate(name):
    m=model(name);chords=set(m['chords']);ws=m['basis_words'];n=len(ws);basis=[gp.mon([w])if w else{():F(1)}for w in ws]
    faces=m['face_words'];fw=faces+[tuple((e,-s)for e,s in reversed(w))for w in faces]
    S=gp.scale(gp.add(*(gp.mon([w])for w in fw)),F(1,2))
    inputs=[gp.mul(S,b)for b in basis]
    gram=[[gp.inner(a,b,chords)for b in basis]for a in basis]
    if gram!=[[F(i==j)for j in range(n)]for i in range(n)]:raise AssertionError('Wilson basis not orthonormal')
    smat=[[gp.inner(a,b,chords)for b in inputs]for a in basis]
    s2=[[gp.inner(a,b,chords)for b in inputs]for a in inputs]
    M=old.sub(s2,old.matmul(smat,smat))
    parts=[];eigen_checks=0;maxterms=0;total_parts=0
    for b in ws:
        d={}
        for w in fw:
            for e,p in gp.spectral_parts(b,w).items():d[e]=gp.add(d.get(e,{}),gp.scale(p,F(1,2)))
        for e,p in list(d.items()):
            norm=gp.inner(p,p,chords)
            if norm<0:raise AssertionError('Negative exact norm')
            if not norm:del d[e];continue
            res=gp.add(gp.electric(p),gp.scale(p,-e));eigen_checks+=1
            if gp.inner(res,res,chords)!=0:raise AssertionError('Electric projector polynomial is not an eigenfunction')
            maxterms=max(maxterms,len(p));total_parts+=1
        if not gp.polynomial_equal_function(gp.add(*d.values()),inputs[len(parts)],chords):raise AssertionError('Energy components fail to sum')
        parts.append(d)
    shells=sorted({e for d in parts for e in d if e>m['cutoff']});mass={}
    for e in shells:
        a=[[gp.inner(inputs[i],parts[j].get(e,{}),chords)for j in range(n)]for i in range(n)]
        if a!=old.transpose(a):raise AssertionError('Energy-resolved Gram not symmetric')
        mass[e]=a
    summed=[[sum((a[i][j]for a in mass.values()),F(0))for j in range(n)]for i in range(n)]
    if summed!=M:raise AssertionError('Resolved hidden energy masses fail complete coupling Gram')
    closure_checks=0
    for j,d in enumerate(parts):
        for e,p in d.items():
            if e>m['cutoff']:continue
            predicted=gp.add(*(gp.scale(basis[i],smat[i][j])for i,E in enumerate(m['energies'])if E==e))
            if not gp.polynomial_equal_function(p,predicted,chords):raise AssertionError('Produced low-energy direction omitted')
            closure_checks+=1
    return m,dict(gram=gram,S=smat,S2=s2,M=M,masses=mass,parts=parts,inputs=inputs,basis=basis,
                  eigenfunction_checks=eigen_checks,low_energy_closure_checks=closure_checks,
                  maximum_terms_in_projector=maxterms,nonzero_energy_components=total_parts,support=support_check(m))

def stringify(a):return [[str(x)for x in row]for row in a]

def export(name):
    m,d=calculate(name);params={k:v for k,v in m.items()if k not in('energies','tail','cutoff')};params.update(energies=list(map(str,m['energies'])),tail=str(m['tail']),cutoff=str(m['cutoff']))
    return dict(model=params,matrices={k:stringify(d[k])for k in('gram','S','S2','M')},
                energy_resolved_masses={str(e):stringify(a)for e,a in d['masses'].items()},
                checks={k:d[k]for k in('eigenfunction_checks','low_energy_closure_checks','maximum_terms_in_projector','nonzero_energy_components','support')},
                scope='Exact finite Haar integrals and electric boundary resolution; full physical cutoff and all-tail interpretation use the written proof.')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--model',choices=['two','strip','corner','cube','vertex_wedge','double_cube'],default='corner');ap.add_argument('--out',type=Path,default=Path('spatial_matrices.json'));a=ap.parse_args();start=time.monotonic();out=export(a.model);out['seconds']=time.monotonic()-start;a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(out,indent=2)+'\n');print(a.model,'dim',len(out['model']['energies']),'shells',list(out['energy_resolved_masses']),'seconds',out['seconds'],flush=True)
if __name__=='__main__':main()
