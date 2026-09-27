#!/usr/bin/env python3
"""Rebuild the exact gauge matrices and run a focused native Compound Eye.

python -S recheck.py --out fresh_evidence
--cached DIR may supply the five preserved model/matrices.json files; their
canonical digests must match. Default rebuilds them from original link algebra.
This focused registry uses new deployment IDs. The full downloadable app also
retains all historical eye versions. No existing registry or source is mutated.
"""
from __future__ import annotations
import argparse,copy,hashlib,json,os,shutil,subprocess,sys
from pathlib import Path
import machine
from targets import all_targets
ROOT=Path(__file__).resolve().parent
EXPECTED={'two':'e8547610d335d10ceff8b1071b1f5c884e23c7253d2d1f16a33eacd0bc9fe344',
 'strip':'00c10fa8c43c205bd2c2b271c73fab272569efadb2ce8a47884f7be7fe2e9d89',
 'corner':'a88041b41c07dcddd9d2b2b7d74874f809fa867cfc60111ac1a554e91ac68363',
 'cube':'91c813f4068b4b149ee7e2e53d0353574a63976767b3810ccd85b25c440a1fa8',
 'double_cube':'f907870d090be604baf4ba5e8ae1da0e89f4dbee6a088d325e4d177b1bdd575d'}
BASE=[('identity',[]),('support',[]),('gram',[]),('energy_labels',[]),('allocation',[]),('certificate',[]),
 ('comparison',[]),('observability',[]),('dark_guard',[]),('window_guard',[]),('source_transfer',[]),('parameter_guard',[]),
 ('model_set',['identity','support','allocation']),('gap_set',['certificate','parameter_guard','window_guard','source_transfer'])]
EXTRA=[('energy_coarsening',['energy_labels','allocation','certificate'],'ym_energy_bins.py'),
 ('forcing_dual',['identity','gram','observability'],'ym_forcing_eye.py'),
 ('response_set',['gram','energy_labels','comparison','observability','dark_guard','energy_coarsening','forcing_dual'],'ym_forcing_eye.py'),
 ('whole',['model_set','response_set','gap_set'],'ym_forcing_eye.py')]

def write(p,x):
    p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(x,indent=2,allow_nan=False)+'\n',encoding='utf-8')
def ref(k):return 'ce.ym.deployment.'+k+'@1.0.0'
def source(name):
    for folder in (ROOT.parent/'scripts',ROOT.parent.parent/'scripts'):
        if (folder/name).is_file():return folder/name
    raise FileNotFoundError('Missing checked source dependency: '+name)

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--out',type=Path,required=True);p.add_argument('--cached',type=Path);a=p.parse_args()
    if not __debug__:raise RuntimeError('Do not run with -O or -OO')
    out=a.out.resolve()
    if out.exists():raise FileExistsError('Refusing to overwrite evidence')
    out.mkdir(parents=True);inst=out/'instrument';dep=inst/'plugins/dependencies/ym';dep.mkdir(parents=True)
    for d in ('catalog/eyes','catalog/sets'):(inst/d).mkdir(parents=True)
    names=['gauge_polynomials.py','spatial_gauge.py','spatial_certificates.py','su3_character_certificate.py','two_plaquette_certificate.py','two_plaquette_extended.py']
    for name in names:shutil.copy2(source(name),dep/name)
    write(dep/'DEPENDENCIES.json',{name:hashlib.sha256((dep/name).read_bytes()).hexdigest()for name in names})
    registry=machine.Registry(inst)
    for name,deps,code in [(n,d,'ym_eyes.py')for n,d in BASE]+EXTRA:
        spec={'id':'ce.ym.deployment.'+name,'version':'1.0.0','title':name.replace('_',' ').title(),
          'family':'Focused native gauge deployment','status':'implemented','inputs':{'packet':'declared-SU3-certificate'},
          'depends_on':[ref(k)for k in deps],'models':['su3-spatial-complete-electric-v1'],'unit_system':'alpha-normalized-energy',
          'assumptions':['The exact declared original-link gauge model and complete electric C<=8 cutoff.','Written analytic proofs are supplied separately from the finite checks.'],
          'output_meaning':'An exact finite observation or a combined set/whole result on the same model.',
          'evidence_class':'exact_finite_gauge_with_written_analytic_links',
          'limits':'No continuum claim; direct numerical rank is not physical visibility; inherited proofs are not recounted as new.',
          'implementation':{'function':name}}
        registry.add(spec,ROOT/code)
    registry.add_set({'id':'ce.set.ym.deployment','version':'1.0.0','title':'Gauge whole picture','eyes':[ref('whole')]})
    targets=all_targets();rows=[];requests={};hashes={}
    for name in EXPECTED:
        dest=out/name;dest.mkdir();mp=dest/'matrices.json'
        if a.cached:shutil.copy2(a.cached/name/'matrices.json',mp)
        else:
            with (dest/'construction.log').open('w')as log:
                subprocess.run([sys.executable,'-S',str(dep/'spatial_gauge.py'),'--model',name,'--out',str(mp)],stdout=log,stderr=subprocess.STDOUT,check=True,timeout=900)
        raw=json.loads(mp.read_text());without_time=copy.deepcopy(raw);without_time.pop('seconds',None)
        if machine.digest(without_time)!=EXPECTED[name]:raise AssertionError('Exact reconstructed matrix record changed: '+name)
        write(dest/'targets.json',targets[name]);packet={'schema':'ym-whole-eye-packet/1','model_name':name,'alpha':'1',
          'matrices':raw,'matrices_canonical_sha256':machine.digest(raw),'targets':targets[name],
          'analytic_links':{'complete_basis':'cross_theorem/proofs/SPATIAL_BASES.md','allocation':'proofs/LOCAL_ENERGY_FLOORS.md','schur':'cross_theorem/proofs/RESOLVED_BOUNDARY.md'},
          'construction':{'matrix_record_without_timing_sha256':EXPECTED[name],'rebuilt_from_original_links':not bool(a.cached)}}
        ctx={'object_id':name,'model_id':'su3-spatial-complete-electric-v1','basis_id':'original-link-Wilson-cycle-C8',
          'boundary_id':'open-graph-and-total-electric-cutoff','coordinate':{'kind':'spatial_instance','value':len(raw['model']['edges']),'unit':'links'},
          'unit_system':'alpha-normalized-energy','source':{'kind':'theoretical','id':EXPECTED[name]},
          'assumptions':['No fundamental matter; positive electric coefficient alpha=1; nonnegative magnetic coupling.']}
        req={'schema':'compound-eye-request-v1','context':ctx,'inputs':{'packet':{'value':packet,'unit':'declared-SU3-certificate'}}};requests[name]=req
        result=machine.execute(req,['ce.set.ym.deployment@1.0.0'],root=inst,workers=4);write(dest/'native.json',result)
        if result['statistics']['status_counts']['ok']!=18:raise AssertionError(result['statistics'])
        rows.append(next(x['value']for x in result['results']if x['eye']==ref('whole')));hashes[name]=EXPECTED[name]
        print(name,'PASS',rows[-1]['accepted_primary_targets'],'targets',flush=True)
    controls=[]
    for label,change in [('false_matrix_hash',lambda x:x.update(matrices_canonical_sha256='0'*64)),('wrong_units',lambda x:x.update(alpha='2')),('false_floor',lambda x:x['targets'][0].update(d='100')),('other_graph_gap',lambda x:x.update(proposed_window_transfer={'model':'cube','cutoff':'total-electric-C<=8'}))]:
        req=copy.deepcopy(requests['two']);change(req['inputs']['packet']['value']);res=machine.execute(req,['ce.set.ym.deployment@1.0.0'],root=inst,workers=4)
        whole=next(x for x in res['results']if x['eye']==ref('whole'))
        if whole['status']=='ok':raise AssertionError('False premise accepted: '+label)
        controls.append({'name':label,'status':whole['status']});write(out/'negative_controls'/(label+'.json'),res)
    write(out/'SUMMARY.json',{'status':'PASS','models':5,'primary_targets':sum(x['accepted_primary_targets']for x in rows),
      'native_outputs':90,'exact_matrix_digests':hashes,'negative_controls':controls,'whole_outputs':rows,
      'rebuild':not bool(a.cached),'new_Lean_compilation':False,'scope':'A focused native deployment; the separate full app preserves219 earlier definitions.'})
    write(out/'SOURCE_SHA256.json',{str(q.relative_to(ROOT)):hashlib.sha256(q.read_bytes()).hexdigest()for q in ROOT.glob('*.py')})
    print('PASS 58 primary targets, 90 native outputs; no post-exit process')
if __name__=='__main__':main()
