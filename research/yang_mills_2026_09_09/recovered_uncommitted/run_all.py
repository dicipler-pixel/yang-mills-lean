#!/usr/bin/env python3
"""Reproduce the 9 September Yang-Mills certificates in an isolated output copy.

python run_all.py                 # standard-library acceptance, no installs
python run_all.py --numerical     # additionally requires NumPy and SciPy

This does not execute Lean locally. Its independent GitHub workflow and source
hashes are recorded in reports/03_lean_acceptance.md. Every output is fresh.
"""
from __future__ import annotations
import argparse,hashlib,json,os,shutil,subprocess,sys,time
from pathlib import Path

ROOT=Path(__file__).resolve().parent

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--numerical',action='store_true')
    ap.add_argument('--out',type=Path,default=ROOT/'fresh_run')
    args=ap.parse_args()
    if not __debug__ or sys.flags.optimize:
        raise RuntimeError('Do not run with -O or -OO: inherited exact verifiers use assertions')
    out=args.out.resolve()
    if out.exists():raise FileExistsError(f'Refusing to overwrite prior evidence: {out}')
    out.mkdir(parents=True);work=out/'work';work.mkdir();logs=out/'logs';logs.mkdir()
    shutil.copytree(ROOT/'scripts',work/'scripts',ignore=shutil.ignore_patterns('__pycache__'))
    if args.numerical:shutil.copytree(ROOT/'tests',work/'tests')
    manifest={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
              for folder in ('scripts','tests','proofs','lean')
              for p in (ROOT/folder).glob('*') if p.is_file()}
    manifest['run_all.py']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    (out/'input_sha256.json').write_text(json.dumps(manifest,indent=2)+'\n')
    env=dict(os.environ,OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1')
    jobs=[('baseline','su3_character_certificate.py',None),
          ('bare','two_plaquette_certificate.py','bare.json'),
          ('allocated','lifted_two_plaquette_certificate.py','allocated.json'),
          ('fifteen','two_plaquette_extended.py','fifteen.json'),
          ('nineteen','two_plaquette_19.py','nineteen.json'),
          ('two_sided','two_sided_spectral_checks.py','two_sided.json'),
          ('local_window','local_window_budget.py','local_window.json'),
          ('scaling','scaling_controls.py','scaling.json'),
          ('spatial','spatial_stability_checks.py','spatial.json')]
    runs=[]
    for name,script,result in jobs:
        cmd=[sys.executable,'-S',str(work/'scripts'/script)]
        if result:cmd+=['--out',str(out/result)]
        start=time.monotonic()
        with (logs/(name+'.log')).open('w') as f:
            p=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,env=env,timeout=600)
        runs.append(dict(name=name,exit_code=p.returncode,seconds=time.monotonic()-start))
        print(name,'PASS' if p.returncode==0 else 'FAIL',flush=True)
        if p.returncode:raise RuntimeError(f'Failed: {name}; see {logs/(name+".log")}')
    for filename in ('su3_results.json','interval_pivot_witnesses.json'):
        shutil.copy2(work/'scripts'/filename,out/filename)
    if args.numerical:
        for name in ('test_local_window','test_su3_independent'):
            cmd=[sys.executable,str(work/'tests'/(name+'.py')),'--out',str(out/(name+'.json'))]
            start=time.monotonic()
            with (logs/(name+'.log')).open('w') as f:
                p=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,env=env,timeout=600)
            runs.append(dict(name=name,exit_code=p.returncode,seconds=time.monotonic()-start))
            print(name,'PASS' if p.returncode==0 else 'FAIL',flush=True)
            if p.returncode:raise RuntimeError(f'Numerical control failed: {name}')
    read=lambda s:json.loads((out/s).read_text())
    baseline=read('su3_results.json');bare=read('bare.json');alloc=read('allocated.json')
    fifteen=read('fifteen.json');nineteen=read('nineteen.json');upper=read('two_sided.json')
    if baseline['total_pivots_checked']!=2275 or baseline['interval_inertia_certificates']!=20:
        raise AssertionError('Changed baseline certificate accounting')
    gaps=sum(len(t['certificates']) for t in (bare,alloc,fifteen,nineteen))
    inertia=3*len(bare['certificates'])+sum(t[k] for t,k in ((alloc,'new_exact_inertia_certificates'),
              (fifteen,'total_inertia_certificates'),(nineteen,'total_inertia_certificates')))
    pivots=21*len(bare['certificates'])+alloc['accepted_pivot_signs']+fifteen['total_pivot_signs']+nineteen['total_pivot_signs']
    if (gaps,inertia,pivots)!=(25,94,6570):raise AssertionError('Changed coupled certificate accounting')
    summary=dict(runs=runs,baseline_inertias=20,baseline_pivots=2275,
                 coupled_lower_gap_certificates=gaps,coupled_lower_inertias=inertia,
                 coupled_lower_pivots=pivots,coupled_upper_enclosures=len(upper['enclosures']),
                 total_new_coupled_inertia_tasks=inertia+upper['new_inertia_calculations'],
                 total_new_coupled_pivots=pivots+upper['new_pivot_signs'],
                 numerical_tests_run=args.numerical,lean_run_by_this_script=False,
                 continuum_mass_gap_claim=False)
    (out/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
    outputs={str(p.relative_to(out)):hashlib.sha256(p.read_bytes()).hexdigest()
             for p in out.rglob('*') if p.is_file()}
    (out/'output_sha256.json').write_text(json.dumps(outputs,indent=2)+'\n')
    print(json.dumps(summary,indent=2));print('Evidence:',out)

if __name__=='__main__':main()
