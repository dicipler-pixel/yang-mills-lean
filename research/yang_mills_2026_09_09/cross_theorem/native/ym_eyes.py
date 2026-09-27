"""Compound Eye gauge observers: exact finite checks with explicit analytic links.

Each output refers to the SAME original-link model and complete electric cutoff.
An energy-resolved comparison measure is not the hidden interacting spectrum.
The native registry schedules these functions; shared results are not votes.
"""
from __future__ import annotations
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
from pathlib import Path
import hashlib, json, sys


def require(b, text):
    if not b: raise ValueError(text)


def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':'),allow_nan=False)
def digest(x):return hashlib.sha256(canonical(x).encode()).hexdigest()


def modules(runtime):
    root=Path(runtime.root)/'plugins/dependencies/ym'
    manifest=json.loads((root/'DEPENDENCIES.json').read_text())
    for name,h in manifest.items():
        require(hashlib.sha256((root/name).read_bytes()).hexdigest()==h,'Dependency changed: '+name)
    if str(root) not in sys.path:sys.path.insert(0,str(root))
    import spatial_gauge as sg
    import spatial_certificates as sc
    import su3_character_certificate as su
    import two_plaquette_certificate as tp
    for mod in (sg,sc,su,tp):
        require(Path(mod.__file__).resolve().parent==root.resolve(),'Dependency imported from another project')
    return sg,sc,su,tp


def prepared(payload,ctx,runtime):
    p=payload['packet']
    def build():
        require(isinstance(p,dict) and p.get('schema')=='ym-whole-eye-packet/1','Wrong gauge packet')
        require(ctx['object_id']==p['model_name'],'Different graph context')
        require(p.get('alpha')=='1','Stored matrices require alpha=1; no silent unit change')
        raw=p['matrices'];require(digest(raw)==p['matrices_canonical_sha256'],'Packet matrix digest mismatch')
        sg,sc,su,tp=modules(runtime);m=sg.model(p['model_name'])
        require(raw['model']['name']==m['name'],'Model label mismatch')
        for key in ('vertices','edges','faces','tree','chords','basis_words','face_words'):
            require(canonical(raw['model'][key])==canonical(m[key]),'Different declared graph/basis: '+key)
        require(raw['model']['energies']==list(map(str,m['energies'])) and F(raw['model']['tail'])==m['tail'] and F(raw['model']['cutoff'])==m['cutoff'],'Different electric spectrum or cutoff')
        n=len(m['energies'])
        def mat(a):
            require(isinstance(a,list) and len(a)==n and all(isinstance(r,list) and len(r)==n for r in a),'Invalid matrix dimension')
            return [[F(x)for x in row]for row in a]
        d={k:mat(raw['matrices'][k])for k in ('gram','S','S2','M')}
        d['masses']={F(e):mat(a)for e,a in raw['energy_resolved_masses'].items()}
        require(d['masses'] and all(e>m['cutoff'] and e>=m['tail'] for e in d['masses']),'Omitted-energy support crosses claimed floor')
        require(all(a==tp.transpose(a) for a in list(d.values()) if isinstance(a,list)),'Non-Hermitian finite comparison')
        for t in p['targets']:
            require(t['model']==m['name'] and t.get('alpha','1')=='1','Target refers to another model/unit')
        require(p['analytic_links']['complete_basis'] and p['analytic_links']['allocation'] and p['analytic_links']['schur'],'Analytic application proof not supplied')
        return m,d
    return runtime.shared('ym_prepared:'+digest(p),build)


def cached(payload,ctx,runtime,name,fn):
    return runtime.shared('ym_'+name+':'+digest(payload['packet']),lambda:fn(*prepared(payload,ctx,runtime)))


def identity(payload,ctx,deps,spec,runtime):
    m,d=prepared(payload,ctx,runtime)
    counts={e:sum(e in [i for i,s in f]for f in m['face_words'])for e in range(len(m['edges']))}
    return dict(graph=m['name'],vertices=len(m['vertices']),links=len(m['edges']),plaquettes=len(m['faces']),independent_cycles=len(m['chords']),retained_dimension=len(m['energies']),cutoff=str(m['cutoff']),omitted_electric_floor=str(m['tail']),link_plaquette_incidence=[counts[e]for e in range(len(m['edges']))],units='alpha=1; lambda/alpha explicit',boundary='open finite graph; not a periodic torus',source=payload['packet']['construction'],scope='Identity, distinct original links and source binding; a hash does not prove the gauge model by itself.')


def support(payload,ctx,deps,spec,runtime):
    def calc(m,d):
        sg,_,_,_=modules(runtime);r=sg.support_check(m)
        n=len(m['energies']);cycles=sum(len(c)<=6 for c in m['cycles'])
        require(n==1+2*cycles,'Cycle-basis count mismatch')
        adj={v:set()for v in m['vertices']}
        for u,v in m['edges']:adj[u].add(v);adj[v].add(u)
        require(all(not(adj[u]&adj[v])for u,v in m['edges']),'Triangle invalidates declared graph class')
        require(all(len(adj[u]&adj[v])<=2 for u,v in combinations(m['vertices'],2)),'K2,3 invalidates declared support theorem')
        return dict(exhaustive_supports=r['tested_edge_subsets'],admissible_small_supports=len(r['all_degree_two_survivors']),complete_C8_dimension=n,counts_by_length={str(k):r['cycle_lengths'].count(k)for k in sorted(set(r['cycle_lengths']))},representation_argument='Gauss forbids degree-one occupied supports; each nontrivial SU3 link costs at least4/3, higher irreps at least3; all <=6-edge admissible supports are simple cycles.',proof='SPATIAL_BASES.md; TWO_PLAQUETTES.md for larger older theta cutoffs',finite_support_test_passed=True,full_tail_is_written_not_Lean=True)
    return cached(payload,ctx,runtime,'support',calc)


def gram(payload,ctx,deps,spec,runtime):
    def calc(m,d):
        _,sc,_,tp=modules(runtime);n=len(m['energies'])
        require(d['gram']==[[F(i==j)for j in range(n)]for i in range(n)],'Selected Wilson basis is not orthonormal')
        require(d['M']==tp.sub(d['S2'],tp.matmul(d['S'],d['S'])),'Boundary Gram not PS2P-(PSP)^2')
        piv=sc.positive_matrix(d['M'])
        return dict(identity='M=PS²P-(PSP)² for this orthonormal complete cutoff',matrix_rank=sum(x>0 for x in piv),dimension=n,trace=str(sum(d['M'][i][i]for i in range(n))),PSD=True,PSD_pivots=list(map(str,piv)),warning='This is a Hamiltonian-coupling Gram. Do not replace it by C_A-C_A² unless C_A is the block of an orthogonal projector.')
    return cached(payload,ctx,runtime,'gram',calc)


def energy_labels(payload,ctx,deps,spec,runtime):
    def calc(m,d):
        _,sc,_,tp=modules(runtime);n=len(m['energies']);summed=[[sum((a[i][j]for a in d['masses'].values()),F(0))for j in range(n)]for i in range(n)]
        require(summed==d['M'],'Resolved masses do not sum to aggregate coupling')
        rows=[]
        for e,a in sorted(d['masses'].items()):
            require(a==tp.transpose(a),'Residue is not symmetric')
            piv=sc.positive_matrix(a);rows.append(dict(energy=str(e),rank=sum(x>0 for x in piv),trace=str(sum(a[i][i]for i in range(n))),pivots=list(map(str,piv))))
        return dict(positive_mass_sum_exact=True,comparison_energy_shells=len(rows),shells=rows,rank_sum=sum(r['rank']for r in rows),naive_denominator_degree=n*len(rows),rank_sensitive_denominator_degree=sum(r['rank']for r in rows),source_connection='Light transition-resolved positive weights; Offset boundary-column support degree',warning='These poles resolve the electric comparison operator, not the exact infinite interacting hidden Hamiltonian.')
    return cached(payload,ctx,runtime,'energies',calc)


def local_results(payload,ctx,runtime):
    def calc(m,d):
        _,sc,su,_=modules(runtime);coef=sc.allocation_coeffs(m);rows=[];unique={}
        for t in payload['packet']['targets']:
            s=F(t['s']);require(0<s<=1,'Invalid electric allocation fraction');off=F(0);local=[]
            if s==1:require(not t['local_floors'],'Bare floor has allocated input')
            else:
                require(len(t['local_floors'])==len(coef),'One local energy floor per face required')
                for c,x in zip(coef,t['local_floors']):
                    kap=(1-s)*c;e=F(x['e']);N=x['N'];require(type(N)is int and N>=1 and F(x['kappa'])==kap and e<kap*su.tail_floor(N),'Invalid local spectral floor')
                    key=(t['lambda'],str(kap),str(e),N)
                    if key not in unique:
                        neg,piv=su.interval_inertia(N,F(t['lambda'])/kap,e/kap,schur=True)
                        require(neg==0 and all(lo>0 for lo,hi in piv),'Local floor positive Schur certificate failed')
                        unique[key]=dict(lambda_=t['lambda'],kappa=str(kap),e=str(e),N=N,pivot_scale=str(su.SCALE),pivots=piv)
                    off+=e;local.append(key)
            floor=s*m['tail']+off;require(F(t['d'])==floor,'Derived all-hidden floor differs')
            rows.append(dict(s=str(s),offset=str(off),floor=str(floor),local_keys=local))
        return dict(allocations=rows,unique_local_certificates=list(unique.values()),one_minus_s_coefficients=list(map(str,coef)),local_bound_interpretation='Absolute ground energy on full cycle-link Hilbert space, extended by spectator identities; not an excitation gap or common local vacuum.',proof='LOCAL_ENERGY_FLOORS.md')
    return cached(payload,ctx,runtime,'allocation',calc)


def allocation(payload,ctx,deps,spec,runtime):return local_results(payload,ctx,runtime)


def exact_targets(payload,ctx,runtime):
    def calc(m,d):
        _,sc,_,_=modules(runtime);locals_=local_results(payload,ctx,runtime);out=[];n=len(m['energies'])
        for t,l in zip(payload['packet']['targets'],locals_['allocations']):
            lam=F(t['lambda']);s=F(t['s']);r=F(t['r']);z=F(t['z']);offset=F(l['offset']);floor=F(l['floor'])
            require(lam>=0 and r<z<floor,'Wrong coupling or r<z<d order')
            A=sc.retained(m,d,lam);pen=sc.correction(m,d,lam,s,offset,z,t['mode'])
            ar=[[A[i][j]-(r if i==j else 0)for j in range(n)]for i in range(n)]
            az=[[A[i][j]-(z if i==j else 0)for j in range(n)]for i in range(n)]
            K=[[az[i][j]-pen[i][j]for j in range(n)]for i in range(n)]
            result=[sc.interval_inertia(x)for x in (ar,az,K)];require([x[0]for x in result]==[1,1,1],'Full target Schur inertia not certified')
            out.append(dict(lambda_=t['lambda'],mode=t['mode'],allocation=t['allocation'],r=str(r),z=str(z),d=str(floor),s=str(s),gap=str(z-r),gap_display=float(z-r),negative_counts=[x[0]for x in result],outer_pivot_intervals=[x[1]for x in result],full_tail='Written domain/inverse-order proof + analytic complete floor + exact finite inertia',uniform_volume_claim=False))
        return dict(accepted=len(out),outer_inertia_tasks=3*len(out),outer_pivots=3*n*len(out),rows=out)
    return cached(payload,ctx,runtime,'targets',calc)


def certificate(payload,ctx,deps,spec,runtime):return exact_targets(payload,ctx,runtime)


def comparison(payload,ctx,deps,spec,runtime):
    def calc(m,d):
        _,sc,_,_=modules(runtime);locals_=local_results(payload,ctx,runtime);n=len(m['energies']);out=[]
        for t,l in zip(payload['packet']['targets'],locals_['allocations']):
            if t['mode']!='resolved' or t['allocation']!='allocated':continue
            lam=F(t['lambda']);s=F(t['s']);z=F(t['z']);off=F(l['offset']);A=sc.retained(m,d,lam)
            mats={k:[[A[i][j]-(z if i==j else 0)-v for j,v in enumerate(row)]for i,row in enumerate(sc.correction(m,d,lam,s,off,z,k))]for k in ('scalar_floor','resolved')}
            inertias={k:sc.interval_inertia(a)[0]for k,a in mats.items()}
            difference=[[mats['resolved'][i][j]-mats['scalar_floor'][i][j]for j in range(n)]for i in range(n)]
            piv=sc.positive_matrix(difference)
            out.append(dict(lambda_=str(lam),same_model_basis_allocation_r_z=True,coarse_negative=inertias['scalar_floor'],resolved_negative=inertias['resolved'],difference_PSD=True,difference_rank=sum(x>0 for x in piv),z=str(z),s=str(s),interpretation='Inertia of sufficient comparison matrices, not physical negative energy levels.'))
        return dict(pairs=out,mechanism='Retain positive coupling masses with their own energies before applying the resolvent weight.')
    return cached(payload,ctx,runtime,'comparison',calc)


def observability(payload,ctx,deps,spec,runtime):
    def calc(m,d):
        _,sc,_,tp=modules(runtime);n=len(m['energies']);M=d['M'];p0=sc.positive_matrix(M)
        A=sc.retained(m,d,F(1));O1=[[x+y for x,y in zip(r,s)]for r,s in zip(M,tp.matmul(tp.matmul(A,M),A))]
        p1=sc.positive_matrix(O1)
        require(all(M[0][j]==0 and M[j][0]==0 for j in range(n)),'Claimed directly dark electric vacuum not dark')
        return dict(lambda_='1',direct_rank=sum(x>0 for x in p0),one_retained_step_rank=sum(x>0 for x in p1),dimension=n,vacuum_first_step_strength=str(O1[0][0]),O1_pivots=list(map(str,p1)),formula='ker(sum A^j M A^j)=intersection ker(B* A^j)',source_connection='Kakeya exact relation-space/dual-obstruction discipline plus positive-Gram kernel identity',warning='Full retained observability does not establish visibility of every omitted physical excitation.')
    return cached(payload,ctx,runtime,'observability',calc)


def dark_guard(payload,ctx,deps,spec,runtime):
    # A boundary-invisible hidden eigenstate can still be the lowest excitation.
    _,sc,_,_=modules(runtime)
    fake=[[F(-1),F(0)],[F(0),F(1)-F(1,100)/9]]
    neg,_=sc.interval_inertia(fake)
    return dict(dark_counterexample=dict(retained_energies=['0','2'],hidden_energies=['1/10','10'],only_coupling='B[1,1]=1/10',misleading_coupled_floor='10',actual_entire_hidden_floor='1/10',false_test_energy='1',coarse_negative_using_false_floor=neg),false_floor_rejected=True,reason='A floor for only coupled modes is not a floor for Q. z must be below the entire hidden spectrum, including invisible modes.',time_memory='B exp(-itD)B* and hidden-initial forcing belong to actual D.',comparison_warning='D>=sC+E* orders resolvents below the spectrum; it does not imply matrix-exponential order or finite-pole exact dynamics.')


def window_guard(payload,ctx,deps,spec,runtime):
    m,d=prepared(payload,ctx,runtime);p=payload['packet'];ext=p.get('proposed_window_transfer')
    if ext is not None:
        require(ext['model']==m['name'] and ext['cutoff']=='total-electric-C<=8','Attempted transfer from a different graph or cutoff')
    return dict(status='SEPARATE_PRODUCT_CUTOFF_COMPARISON_NOT_INSTANTIATED',missing=['Compression gap for the same spatial operator and product link cutoff','S<1 and the certified error budget for that same cutoff','Volume/physical-scale uniformity of the resulting margin'],current_certificate='Uses a total-electric cutoff and complete-tail Schur comparison; no extra local-window error subtraction is required for that certificate.',warning='Do not compare a large-lattice error against a gap borrowed from one plaquette, the strip, or the cube.')


def source_transfer(payload,ctx,deps,spec,runtime):
    prepared(payload,ctx,runtime)
    return dict(used=[{'source':'Light research edition3, §§4.8–4.9','content':'Energy-resolved positive transition weights; equality of silent directions under positive weighting','gauge_use':'Positive Casimir masses, ordered resolvent weights and kernel guards'},{'source':'Elemental peeling exact elimination','content':'Memory kernel plus initial hidden force','gauge_use':'Separate true D spectral measure from finite electric comparison'},{'source':'Arithmetic Kakeya/forcing','content':'Actual relation space and dual obstruction, not rank only','gauge_use':'Krylov/observability kernel; different support orientation at equal rank'},{'source':'Offset/Laurent boundary support','content':'Determinant degree bounded by rank of parameter support','gauge_use':'Sufficient rational denominator exponents bounded by residue ranks'}],not_transferred=['Optical material calibration','Sine law or scalar parity for arbitrary gauge generators','Kakeya exponent or forcing score as an energy inequality','Counts of old Lean statements as new gauge proofs'],all_historical_eyes_preserved_not_all_applicable=True)


def parameter_guard(payload,ctx,deps,spec,runtime):
    m,d=prepared(payload,ctx,runtime);p=len(m['faces']);rows=exact_targets(payload,ctx,runtime)['rows'];best={}
    for r in rows:
        key=r['lambda_']
        if key not in best or F(r['gap'])>F(best[key]['gap']):best[key]=r
    width=F(1,20);intervals=[]
    for key,r in best.items():
        lam=F(key);g=F(r['gap']);margin=g-F(9,2)*p*width
        if lam>=width and margin>0:intervals.append(dict(center=str(lam),half_width=str(width),coupling_interval=[str(lam-width),str(lam+width)],gap_lower=str(margin),common_alpha_rescaling='Multiply this bound by alpha>0 while keeping lambda/alpha in this interval.'))
    return dict(lipschitz_coefficient=str(F(9,2)*p),intervals=intervals,proof='PARAMETER_AND_POLE_BOUNDS.md; bounded magnetic perturbation and min-max.',volume_uniform=False,continuum_trajectory_derived=False)


def vals(deps):return {k.split('@')[0].split('.')[-1]:v['value']for k,v in deps.items()}


def model_set(payload,ctx,deps,spec,runtime):
    v=vals(deps)
    return dict(title='Gauge space and complete tail',graph=v['identity'],support=v['support'],allocation={'coefficients':v['allocation']['one_minus_s_coefficients'],'unique_floor_checks':len(v['allocation']['unique_local_certificates'])},findings=['Complete electric subspace is tied to original graph supports, not an arbitrary Wilson-loop list.','Local absolute-energy bounds add without a common local vacuum.'],missing=['Uniform growth in number of cells is not proved.'])


def response_set(payload,ctx,deps,spec,runtime):
    v=vals(deps)
    return dict(title='Boundary response, energy and exact span',gram=v['gram'],energies=v['energy_labels'],pairs=v['comparison'],observability=v['observability'],dark_guard=v['dark_guard'],findings=['An aggregate Gram loses energy labels.','Directly silent is not necessarily dynamically decoupled.','A boundary-dark hidden level still belongs in the spectral floor.'],missing=['Full interacting memory is not replaced by the finite comparison poles.'])


def gap_set(payload,ctx,deps,spec,runtime):
    v=vals(deps);r=v['certificate']
    return dict(title='Certificates and physical scale',accepted=r['accepted'],outer_inertia_tasks=r['outer_inertia_tasks'],outer_pivots=r['outer_pivots'],bounds=[{k:x[k]for k in ('lambda_','mode','allocation','gap','gap_display','s')}for x in r['rows']],parameter=v['parameter_guard'],window=v['window_guard'],source_transfer=v['source_transfer'],missing=v['window_guard']['missing'])


def whole(payload,ctx,deps,spec,runtime):
    v=vals(deps);a,b,c=v['model_set'],v['response_set'],v['gap_set'];o=b['observability'];pairs=b['pairs']['pairs']
    findings=[]
    if any(p['coarse_negative']>1 and p['resolved_negative']==1 for p in pairs):findings.append('ENERGY_LABELS_CHANGE_CERTIFICATE_ACCEPTANCE_AT_IDENTICAL_TEST_PARAMETERS')
    if o['direct_rank']<o['one_retained_step_rank']:findings.append('ONE_STEP_EXPOSES_A_DIRECTLY_SILENT_RETAINED_DIRECTION')
    if b['energies']['rank_sensitive_denominator_degree']<b['energies']['naive_denominator_degree']:findings.append('BOUNDARY_SUPPORT_REDUCES_SUFFICIENT_POLE_DEGREE')
    return dict(schema='compound-eye-gauge-whole/1',model=a['graph']['graph'],sets=[a,b,c],findings=findings,accepted_finite_targets=c['accepted'],missing=list(dict.fromkeys(a['missing']+b['missing']+c['missing'])),next_required='Control a gap for growing spatial systems in a consistent physical normalization; do not reuse a different model\'s gap.',continuum_mass_gap_proved=False,independent_votes=0,scope='Native multi-observer computation on a declared finite graph; analytic links and verification levels remain separate.')
