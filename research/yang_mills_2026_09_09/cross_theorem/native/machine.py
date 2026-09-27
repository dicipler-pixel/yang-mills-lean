#!/usr/bin/env python3
"""Compound Eye modular instrument 1.0. Registry, dependency DAG, and evidence records.

This orchestrator is standard-library Python. Numerical plugins require the pinned
dependencies. An eye is an explicitly scoped calculation, not an independent vote.
"""
from concurrent.futures import ThreadPoolExecutor, Future
from copy import deepcopy
from pathlib import Path
import argparse, hashlib, importlib.util, json, math, re, sys, threading, time

ROOT=Path(__file__).resolve().parent
VERSION='1.0.1'
KINDS={'acquisition','calibration','processed','evaluated','inferred','synthetic','theoretical'}

def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':'),allow_nan=False)
def digest(x):return hashlib.sha256(canonical(x).encode()).hexdigest()
def filehash(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(condition,message):
    if not condition:raise ValueError(message)
def reference(spec):return spec['id']+'@'+spec['version']
def safe_path(root,rel):
    path=(Path(root)/rel).resolve()
    need(path.is_relative_to(Path(root).resolve()),'Path leaves project directory.')
    return path
def dump(path,value):
    p=Path(path);p.parent.mkdir(parents=True,exist_ok=True)
    temp=p.with_suffix(p.suffix+'.tmp');temp.write_text(json.dumps(value,indent=2,allow_nan=False)+'\n');temp.replace(p)

class Registry:
    def __init__(self,root=ROOT):
        self.root=Path(root).resolve();self.eyes={};self.sets={}
        self.verify_history()
        for p in sorted((self.root/'catalog/eyes').glob('*.json')):
            spec=json.loads(p.read_text());self.validate(spec);key=reference(spec)
            need(key not in self.eyes,'Duplicate eye version: '+key);self.eyes[key]=spec
        for p in sorted((self.root/'catalog/sets').glob('*.json')):
            spec=json.loads(p.read_text());key=reference(spec)
            need(key not in self.sets,'Duplicate set version.');self.sets[key]=spec
        ledger=self.root/'catalog/set_history.jsonl';self.set_history=[];previous='0'*64
        if ledger.exists():
            for line in ledger.read_text().splitlines():
                row=json.loads(line);given=row.pop('event_sha256')
                need(row['previous']==previous and row['sequence']==len(self.set_history) and digest(row)==given,'Broken set-version history.')
                row['event_sha256']=given;self.set_history.append(row);previous=given
        logged_sets={row['set']:row['manifest_sha256'] for row in self.set_history}
        need(set(logged_sets)==set(self.sets),'Set history and inventory disagree.')
        for k,s in self.sets.items():need(digest(s)==logged_sets[k],'A pinned eye set changed: '+k)
        # Every eye, including retired versions, must still match its registration.
        logged={row['eye']:row['manifest_sha256'] for row in self.history}
        need(set(logged)==set(self.eyes),'Registry history and eye inventory disagree.')
        for k,v in self.eyes.items():need(logged[k]==digest(v),'Registered definition changed: '+k)

    def validate(self,spec):
        for key in ['id','version','title','family','status','inputs','depends_on','assumptions','output_meaning','evidence_class','limits','implementation']:
            need(key in spec,'Missing eye field: '+key)
        need(re.fullmatch(r'[a-z][a-z0-9_.-]+',spec['id']) is not None,'Invalid stable eye ID.')
        need(re.fullmatch(r'\d+\.\d+\.\d+',spec['version']) is not None,'Use an explicit semantic version.')
        need(spec['status'] in ['implemented','specified','archived_result'],'Invalid implementation status.')
        need(isinstance(spec['inputs'],dict) and isinstance(spec['depends_on'],list),'Malformed contract.')
        impl=spec['implementation']
        if impl is not None:
            need(safe_path(self.root,impl['path']).is_file(),'Implementation file missing.')
            need(filehash(safe_path(self.root,impl['path']))==impl['sha256'],'Implementation hash mismatch.')
        else:need(spec['status']=='specified','Runnable eye has no implementation.')

    def verify_history(self):
        p=self.root/'catalog/history.jsonl';self.history=[];prev='0'*64
        if not p.exists():return
        for line in p.read_text().splitlines():
            row=json.loads(line);given=row.pop('event_sha256')
            need(row['sequence']==len(self.history) and row['previous']==prev,'Broken registry history.')
            need(digest(row)==given,'Registry history hash mismatch.')
            row['event_sha256']=given;self.history.append(row);prev=given

    def selection(self,names):
        refs=[]
        for name in names:
            if name in self.sets:refs.extend(self.sets[name]['eyes'])
            else:refs.append(name)
        refs=list(dict.fromkeys(refs));visiting=set();ordered=[];seen=set()
        def add(ref):
            need(ref in self.eyes,'Unknown or unpinned eye: '+ref)
            need(ref not in visiting,'Dependency cycle detected at '+ref)
            if ref in seen:return
            visiting.add(ref)
            for dep in self.eyes[ref]['depends_on']:add(dep)
            visiting.remove(ref);seen.add(ref);ordered.append(ref)
        for ref in refs:add(ref)
        ids=[self.eyes[r]['id'] for r in ordered]
        need(len(ids)==len(set(ids)),'Conflicting versions of the same eye in one run.')
        return refs,ordered

    def add(self,spec,code=None):
        spec=deepcopy(spec);key=reference(spec)
        need(key not in self.eyes,'An existing eye version cannot be replaced; add a new version.')
        if code is not None:
            data=Path(code).read_bytes();h=hashlib.sha256(data).hexdigest()
            rel='plugins/installed/'+h+'.py';p=safe_path(self.root,rel);p.parent.mkdir(parents=True,exist_ok=True)
            if not p.exists():p.write_bytes(data)
            spec['implementation']={'path':rel,'sha256':h,'function':spec['implementation']['function']}
        self.validate(spec)
        for dep in spec['depends_on']:need(dep in self.eyes,'Register dependency first: '+dep)
        need(key not in spec['depends_on'],'An eye cannot depend on itself.')
        path=self.root/'catalog/eyes'/(key+'.json');need(not path.exists(),'Version file already exists.')
        row={'sequence':len(self.history),'previous':self.history[-1]['event_sha256'] if self.history else '0'*64,
             'action':'register','eye':key,'manifest_sha256':digest(spec)}
        row['event_sha256']=digest(row)
        dump(path,spec)
        with (self.root/'catalog/history.jsonl').open('a') as f:f.write(canonical(row)+'\n')
        self.eyes[key]=spec;self.history.append(row)
        return {'registered':key,'history_sequence':row['sequence']}

    def add_set(self,spec):
        key=reference(spec);need(key not in self.sets,'Existing set versions cannot be replaced.')
        need(re.fullmatch(r'[a-z][a-z0-9_.-]+',spec['id']) is not None and re.fullmatch(r'\d+\.\d+\.\d+',spec['version']) is not None,'Invalid set identifier or version.')
        need(isinstance(spec.get('eyes'),list) and spec['eyes'],'A set must name pinned eyes.')
        self.selection(spec['eyes'])
        row={'sequence':len(self.set_history),'previous':self.set_history[-1]['event_sha256'] if self.set_history else '0'*64,
             'action':'register_set','set':key,'manifest_sha256':digest(spec)}
        row['event_sha256']=digest(row)
        dump(self.root/'catalog/sets'/(key+'.json'),spec)
        with (self.root/'catalog/set_history.jsonl').open('a') as f:f.write(canonical(row)+'\n')
        self.sets[key]=deepcopy(spec);self.set_history.append(row);return {'registered_set':key}

class Runtime:
    def __init__(self,root):
        self.root=root;self.lock=threading.Lock();self.cache={};self.calls={};self.hits=0
    def shared(self,key,compute):
        with self.lock:
            owner=key not in self.cache
            if owner:self.cache[key]=Future();self.calls[key.split(':')[0]]=self.calls.get(key.split(':')[0],0)+1
            else:self.hits+=1
            future=self.cache[key]
        if owner:
            try:future.set_result(compute())
            except BaseException as exc:future.set_exception(exc)
        return deepcopy(future.result())

class SourceRuntime:
    """A preserved adapter's source layout, sharing the current run's cache.

    This changes file resolution only. Registered implementation bytes, requests,
    results, dependency scheduling and cache keys remain those of the active run.
    """
    def __init__(self, runtime, root):
        self.root=root
        self.shared=runtime.shared

def validate_context(ctx):
    for key in ['object_id','model_id','basis_id','boundary_id','coordinate','unit_system','source','assumptions']:
        need(key in ctx,'Context missing '+key)
    for k in ['object_id','model_id','basis_id','boundary_id','unit_system']:need(isinstance(ctx[k],str) and ctx[k],'Empty context identity.')
    c=ctx['coordinate'];need(set(c)=={'kind','value','unit'},'Coordinate needs kind, value, unit.')
    need(type(c['value']) in (int,float) and math.isfinite(c['value']),'Invalid coordinate value.')
    need(ctx['source']['kind'] in KINDS and bool(ctx['source']['id']),'Invalid source layer.')
    need(isinstance(ctx['assumptions'],list),'Assumptions must be explicit list.')
    canonical(ctx)

def execute(request,selected,root=ROOT,workers=4):
    reg=Registry(root);ctx=deepcopy(request['context']);validate_context(ctx)
    model_path=reg.root/'catalog/models.json'
    model_contracts=json.loads(model_path.read_text()) if model_path.exists() else {}
    contract=model_contracts.get(ctx['model_id'])
    if contract:
        for k in ['basis_id','boundary_id','unit_system']:
            need(ctx[k]==contract[k],'Context contradicts the implemented model: '+k)
        for k in ['kind','unit']:
            need(ctx['coordinate'][k]==contract['coordinate'][k],'Coordinate convention contradicts the implemented model.')
    need(type(workers) is int and 1<=workers<=32,'Workers must be 1..32.')
    need(request.get('schema')=='compound-eye-request-v1','Wrong request schema.')
    inputs=deepcopy(request.get('inputs',{}));canonical(inputs)
    for key,item in inputs.items():
        need(isinstance(item,dict) and 'value' in item and isinstance(item.get('unit'),str),'Every input needs value and unit: '+key)
        if 'context' in item:need(item['context']==ctx,'Incompatible input context: '+key)
    requested,order=reg.selection(selected);runtime=Runtime(reg.root);results={};layers=[];modules={};mlock=threading.Lock()
    started=time.perf_counter()
    def invoke(ref):
        spec=reg.eyes[ref];base={'eye':ref,'context_sha256':digest(ctx),'definition_sha256':digest(spec),
            'evidence_class':spec['evidence_class'],'input_source_kind':ctx['source']['kind'],
            'assumptions':list(dict.fromkeys(ctx['assumptions']+spec['assumptions'])),
            'dependencies':spec['depends_on'],'limits':spec['limits']}
        if spec['status']=='specified':return dict(base,status='blocked',reason='Specified eye: required implementation or physical input is not available.')
        if spec.get('unit_system','any') not in ('any',ctx['unit_system']):return dict(base,status='inapplicable',reason='Unit convention is incompatible with this eye.')
        if spec.get('models') and ctx['model_id'] not in spec['models']:return dict(base,status='inapplicable',reason='This eye is scoped to a different model.')
        missing=[k for k in spec['inputs'] if k not in inputs]
        if missing:return dict(base,status='blocked',reason='Missing inputs: '+', '.join(missing))
        for k,unit in spec['inputs'].items():
            if unit!='*' and inputs[k]['unit']!=unit:return dict(base,status='inapplicable',reason='Unconverted input units: '+k)
        deps={k:results[k] for k in spec['depends_on']}
        if any(x['status']!='ok' for x in deps.values()):return dict(base,status='blocked',reason='A required eye did not return usable output.')
        impl=spec['implementation'];path=safe_path(reg.root,impl['path'])
        try:
            with mlock:
                if impl['sha256'] not in modules:
                    m=importlib.util.spec_from_file_location('eye_'+impl['sha256'],path);mod=importlib.util.module_from_spec(m);m.loader.exec_module(mod);modules[impl['sha256']]=mod
                handler=getattr(modules[impl['sha256']],impl['function'])
            payload={k:deepcopy(inputs[k]['value']) for k in spec['inputs']}
            source_runtime=runtime
            if impl['path']=='plugins/eyes.py' and not (runtime.root/'preserved/compound-eye-0.4').is_dir():
                source_root=runtime.root/'preserved/original_modular_release'
                need((source_root/'preserved/compound-eye-0.4').is_dir(),'Preserved legacy source layout is missing.')
                source_runtime=SourceRuntime(runtime,source_root)
            output=handler(payload,deepcopy(ctx),deepcopy(deps),deepcopy(spec),source_runtime)
            canonical(output)
            if isinstance(output,dict) and output.get('_status')=='blocked':return dict(base,status='blocked',reason=output['reason'])
            return dict(base,status='ok',value=output,value_sha256=digest(output))
        except Exception as exc:return dict(base,status='error',reason=type(exc).__name__+': '+str(exc))
    remaining=set(order)
    while remaining:
        ready=[r for r in order if r in remaining and all(d in results for d in reg.eyes[r]['depends_on'])]
        need(ready,'Dependency DAG cannot advance.')
        with ThreadPoolExecutor(max_workers=workers) as pool:
            rows=list(pool.map(invoke,ready))
        for r,row in zip(ready,rows):results[r]=row;remaining.remove(r)
        layers.append(ready)
    report={'schema':'compound-eye-run-v1','engine_version':VERSION,'request_sha256':digest(request),'model_contracts_sha256':digest(model_contracts),
        'context':ctx,'context_sha256':digest(ctx),'requested':requested,'expanded':order,'dependency_layers':layers,
        'results':[results[r] for r in order],'statistics':{'eyes_requested':len(requested),'eyes_executed':len(order),
        'status_counts':{s:sum(v['status']==s for v in results.values()) for s in ['ok','blocked','inapplicable','error']},
        'shared_kernel_calls':runtime.calls,'shared_cache_hits':runtime.hits,'workers':workers,'seconds':time.perf_counter()-started},
        'scope':'Scoped computations. Source labels are declarations; hashes verify bytes, not measurement authenticity. Shared evidence is not counted as independent confirmation.'}
    report['result_sha256']=digest(report['results']);return report

def save_run(root,result):
    # Exclusive file creation prevents repeated execution from overwriting evidence.
    p=Path(root)/'runs'/f'{time.time_ns()}_{result["request_sha256"][:12]}.json'
    p.parent.mkdir(exist_ok=True)
    with p.open('x') as f:f.write(json.dumps(result,indent=2,allow_nan=False)+'\n')
    return p

def main():
    parser=argparse.ArgumentParser(description=__doc__);sub=parser.add_subparsers(dest='command',required=True)
    sub.add_parser('catalog');sub.add_parser('verify-preservation')
    p=sub.add_parser('run');p.add_argument('request');p.add_argument('--sets',nargs='+',required=True);p.add_argument('--workers',type=int,default=4);p.add_argument('--output')
    p=sub.add_parser('add-eye');p.add_argument('manifest');p.add_argument('--code')
    p=sub.add_parser('add-set');p.add_argument('manifest')
    args=parser.parse_args()
    try:
        if args.command=='catalog':
            r=Registry();out={'eyes':[{'ref':k,'title':s['title'],'family':s['family'],'status':s['status']} for k,s in r.eyes.items()], 'sets':r.sets}
        elif args.command=='add-eye':out=Registry().add(json.loads(Path(args.manifest).read_text()),args.code)
        elif args.command=='add-set':out=Registry().add_set(json.loads(Path(args.manifest).read_text()))
        elif args.command=='verify-preservation':
            data=json.loads((ROOT/'preservation_manifest.json').read_text())
            for row in data['files']:need(filehash(safe_path(ROOT,row['preserved_path']))==row['sha256'],'Preserved source changed: '+row['preserved_path'])
            r=Registry();out={'all_passed':True,'preserved_files':len(data['files']),'registered_versions':len(r.eyes),'history_events':len(r.history),'scope':data['scope']}
        else:
            request=json.load(sys.stdin) if args.request=='-' else json.loads(Path(args.request).read_text())
            out=execute(request,args.sets,workers=args.workers);saved=save_run(ROOT,out)
            if args.output:dump(args.output,out)
            print(json.dumps({'saved_run':str(saved),'statistics':out['statistics'],'result_sha256':out['result_sha256']},indent=2))
            return 2 if out['statistics']['status_counts']['error'] else 0
        print(json.dumps(out,indent=2));return 0
    except (ValueError,KeyError,TypeError,OSError) as exc:
        print(json.dumps({'status':'invalid_request_or_registry','reason':str(exc)}));return 2

if __name__=='__main__':raise SystemExit(main())
