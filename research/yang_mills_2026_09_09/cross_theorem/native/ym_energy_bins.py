"""A new native eye: safe energy coarsening through positive chord bounds.

This is a coarser sufficient certificate, not an averaged-energy ansatz. Existing
observer versions remain unchanged; only response/whole receive new versions.
"""
from fractions import Fraction as F

def need(b,s):
    if not b:raise ValueError(s)

def values(d):return {k.split('@')[0].split('.')[-1]:v['value']for k,v in d.items()}

def energy_coarsening(payload,ctx,deps,spec,runtime):
    import spatial_certificates as sc
    import spatial_gauge as sg
    import two_plaquette_certificate as tp
    packet=payload['packet'];name=packet['model_name']
    if name not in ('cube','double_cube'):
        return {'available':False,'reason':'This bounded coarsening experiment targets the two three-dimensional cube instances only.'}
    need(all(v['status']=='ok'for v in deps.values()),'Prerequisite matrix/tail certificate missing')
    m=sg.model(name);raw=packet['matrices'];d={k:[[F(x)for x in r]for r in raw['matrices'][k]]for k in ('S','M')};d['masses']={F(e):[[F(x)for x in r]for r in a]for e,a in raw['energy_resolved_masses'].items()}
    lam=F(1)if name=='cube'else F(1,2);margin=F(2)if name=='cube'else F(7,2);nb=3 if name=='cube'else 2
    t=next(t for t in packet['targets']if F(t['lambda'])==lam and t['mode']=='resolved'and t['allocation']=='allocated')
    s=F(t['s']);off=sum(F(e['e'])for e in t['local_floors']);r=F(t['r']);z=r+margin;floor=F(t['d']);need(r<z<F(t['z'])<floor,'Coarsened test must sit below its accepted parent target')
    es=sorted(d['masses']);n=len(m['energies']);bins=[es[len(es)*i//nb:len(es)*(i+1)//nb]for i in range(nb)];pen=[[F(0)for _ in range(n)]for _ in range(n)];records=[]
    for block in bins:
        lo,hi=block[0],block[-1];a=s*lo+off-z;b=s*hi+off-z;need(a>0 and b>=a,'Nonpositive energy interval')
        mass=[[sum(d['masses'][e][i][j]for e in block)for j in range(n)]for i in range(n)]
        moment=[[sum(e*d['masses'][e][i][j]for e in block)for j in range(n)]for i in range(n)]
        for i in range(n):
            for j in range(n):pen[i][j]+=lam*lam*((s*(lo+hi)+off-z)*mass[i][j]-s*moment[i][j])/(a*b)
        scalar_checks=[]
        for e in block:
            x=s*e+off-z;chord=(a+b-x)/(a*b);diff=chord-1/x
            need(diff==(x-a)*(b-x)/(a*b*x)>=0,'Incorrect inverse chord bound')
            scalar_checks.append({'energy':str(e),'inverse':str(1/x),'upper':str(chord),'error':str(diff)})
        records.append({'energies':list(map(str,block)),'M0':list(map(lambda r:list(map(str,r)),mass)),'M1':list(map(lambda r:list(map(str,r)),moment)),'weight_checks':scalar_checks})
    exact=sc.correction(m,d,lam,s,off,z,'resolved');coarse=sc.correction(m,d,lam,s,off,z,'scalar_floor')
    need(all(x>=0 for x in sc.positive_matrix(tp.sub(pen,exact))),'Moment bound is below exact resolved penalty')
    need(all(x>=0 for x in sc.positive_matrix(tp.sub(coarse,pen))),'Coarsening worse than the all-floor comparison')
    A=sc.retained(m,d,lam)
    ar=[[A[i][j]-(r if i==j else 0)for j in range(n)]for i in range(n)];az=[[A[i][j]-(z if i==j else 0)for j in range(n)]for i in range(n)];K=tp.sub(az,pen)
    checked=[sc.interval_inertia(x)for x in (ar,az,K)];need([v[0]for v in checked]==[1,1,1],'Coarsened gap comparison did not certify one low eigenvalue')
    coarse_negative=sc.interval_inertia(tp.sub(az,coarse))[0]
    return {'available':True,'model':name,'lambda_':str(lam),'r':str(r),'z':str(z),'gap_lower':str(margin),'parent_stronger_gap':str(F(t['z'])-r),'original_residue_matrices':len(es),'energy_bins':nb,'moment_matrices':2*nb,'bin_records':records,'negative_counts':[v[0]for v in checked],'pivot_intervals':[v[1]for v in checked],'same_point_all_floor_negative':coarse_negative,'ordered_penalty_checks':True,'interpretation':'Fewer energy descriptors certify a weaker but positive gap. This is not a speed benchmark, a mean-energy substitution, or a new spatial-volume theorem.'}

def response_set(payload,ctx,deps,spec,runtime):
    v=values(deps)
    out=dict(title='Boundary response, energy and exact span',gram=v['gram'],energies=v['energy_labels'],pairs=v['comparison'],observability=v['observability'],dark_guard=v['dark_guard'],coarsening=v['energy_coarsening'],findings=['An aggregate Gram loses energy labels.','Directly silent is not necessarily dynamically decoupled.','A boundary-dark hidden level still belongs in the spectral floor.'],missing=['Full interacting memory is not replaced by the finite comparison poles.'])
    if v['energy_coarsening']['available']:out['findings'].append('Positive two-moment bins keep a sufficient certificate with fewer energy descriptors.')
    return out

def whole(payload,ctx,deps,spec,runtime):
    v=values(deps);a,b,c=v['model_set'],v['response_set'],v['gap_set'];obs=b['observability'];findings=[]
    if any(p['coarse_negative']>1 and p['resolved_negative']==1 for p in b['pairs']['pairs']):findings.append('ENERGY_LABELS_CHANGE_ACCEPTANCE_AT_THE_SAME_TEST_POINT')
    if obs['direct_rank']<obs['one_retained_step_rank']:findings.append('A_DIRECTLY_SILENT_RETAINED_DIRECTION_BECOMES_VISIBLE_AFTER_DYNAMICS')
    if b['coarsening']['available']:findings.append('ENERGY_MOMENTS_CAN_BE_COMPRESSED_WITH_A_PROVED_ONE_SIDED_ERROR')
    return {'schema':'compound-eye-gauge-whole/1.1','model':a['graph']['graph'],'sets':[a,b,c],'findings':findings,'accepted_primary_targets':c['accepted'],'additional_moment_comparison':b['coarsening']['available'],'missing':list(dict.fromkeys(a['missing']+b['missing']+c['missing'])),'continuum_mass_gap_proved':False,'independent_votes':0,'scope':'13 observers, three set outputs, one whole output; exact finite gauge certificates plus separate written analytic links.'}
