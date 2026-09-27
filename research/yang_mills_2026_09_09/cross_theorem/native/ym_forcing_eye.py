"""Exact native application of the pinned Kakeya dual-obstruction theorem.
CanForce means an invisible target-changing vector; factorization excludes it.
The physical hidden Hilbert space is not replaced by this retained algebra.
"""
from fractions import Fraction as F
import spatial_certificates as sc
import spatial_gauge as sg

def solve(a,b):
    a=[r[:] for r in a];b=b[:];n=len(a)
    for k in range(n):
        if a[k][k]<=0:raise ArithmeticError('Expected positive rational elimination pivot')
        for i in range(k+1,n):
            if not a[i][k]:continue
            f=a[i][k]/a[k][k]
            for j in range(k+1,n):a[i][j]-=f*a[k][j]
            b[i]-=f*b[k];a[i][k]=F(0)
    x=[F(0)]*n
    for i in reversed(range(n)):x[i]=(b[i]-sum(a[i][j]*x[j]for j in range(i+1,n)))/a[i][i]
    return x


def certificate(m,d):
    M=d['M'];A=sc.retained(m,d,F(1));n=len(M)
    C=[[sum(M[i][k]*A[k][j]for k in range(n))for j in range(n)]for i in range(n)]
    if any(M[i][0]or M[0][i]for i in range(n)):raise ValueError('Electric vacuum not a direct kernel vector')
    j=next(i for i in range(1,n)if C[i][0]);c=C[j][0]
    second=[F(i==j)/c for i in range(n)]
    rhs=[F(i==0)-C[j][i]/c for i in range(n)]
    if rhs[0]!=0:raise AssertionError('Vacuum cancellation failed')
    first=[F(0)]+solve([row[1:]for row in M[1:]],rhs[1:])
    output=[sum(first[k]*M[k][i]+second[k]*C[k][i]for k in range(n))for i in range(n)]
    if output!=[F(i==0)for i in range(n)]:raise AssertionError('Dual row does not factor the target')
    damaged=first[:];damaged[1]+=1
    wrong=[sum(damaged[k]*M[k][i]+second[k]*C[k][i]for k in range(n))for i in range(n)]
    if wrong==output:raise AssertionError('A corrupted dual certificate was not detected')
    return {'model':m['name'],'dimension':n,'lambda_for_retained_generator':'1','target':'electric vacuum coordinate b(x)=x[0]','direct_CanForce_witness':['1']+['0']*(n-1),'direct_constraint':'M','stacked_constraint':'Theta=[M; M A]','dual_first':list(map(str,first)),'dual_second':list(map(str,second)),'factorization_result':list(map(str,output)),'exact_scalar_identities':n,'corrupted_dual_rejected':True,'nonzero_dual_entries':sum(x!=0 for x in first+second),'Kakeya_theorem':'OperatorFirst.KakeyaForcingLinear.dual_certificate at41fbf3b9e6ad8143d597928e477a9d94adb6d6d6','conclusion':'CanForce(M,b), but NOT CanForce(Theta,b).','warning':'Kakeya CanForce means an invisible target-changing vector exists, not that observations determine the target. The stacked map is retained-generator algebra, not an uncontrolled time derivative with unknown hidden forcing.'}



def forcing_dual(payload,ctx,deps,spec,runtime):
    if any(v['status']!='ok' for v in deps.values()):raise ValueError('Missing gauge, Gram or observability premise')
    p=payload['packet'];m=sg.model(p['model_name'])
    d={k:[[F(x)for x in row]for row in p['matrices']['matrices'][k]]for k in ('M','S')}
    out=certificate(m,d);out['available']=True;return out

def values(deps):return {k.split('@')[0].split('.')[-1]:v['value']for k,v in deps.items()}

def response_set(payload,ctx,deps,spec,runtime):
    v=values(deps)
    return dict(title='Boundary response, energy and exact span',gram=v['gram'],energies=v['energy_labels'],
      pairs=v['comparison'],observability=v['observability'],dark_guard=v['dark_guard'],
      coarsening=v['energy_coarsening'],forcing_dual=v['forcing_dual'],
      findings=['Energy labels change the certificate without enlarging the retained basis.',
      'Direct silence need not persist under the retained generator.',
      'The exact target-factorization witness distinguishes rank from what observations determine.',
      'The entire hidden spectrum includes boundary-invisible excitations.'],
      missing=['Full interacting memory is not replaced by finite comparison poles.'])

def whole(payload,ctx,deps,spec,runtime):
    v=values(deps);a,b,c=v['model_set'],v['response_set'],v['gap_set'];findings=[]
    if any(p['coarse_negative']>1 and p['resolved_negative']==1 for p in b['pairs']['pairs']):findings.append('ENERGY_LABELS_CHANGE_ACCEPTANCE_AT_IDENTICAL_PARAMETERS')
    if b['observability']['direct_rank']<b['observability']['one_retained_step_rank']:findings.append('RETAINED_DYNAMICS_EXPOSES_A_DIRECTLY_SILENT_DIRECTION')
    if b['coarsening']['available']:findings.append('POSITIVE_ENERGY_MOMENTS_KEEP_A_WEAKER_CERTIFICATE')
    if b['forcing_dual']['available']:findings.append('KAKEYA_DUAL_THEOREM_HAS_AN_EXACT_GAUGE_INSTANCE')
    return dict(schema='compound-eye-gauge-whole/1.2',model=a['graph']['graph'],sets=[a,b,c],findings=findings,
      accepted_primary_targets=c['accepted'],additional_moment_comparison=b['coarsening']['available'],
      missing=list(dict.fromkeys(a['missing']+b['missing']+c['missing'])),continuum_mass_gap_proved=False,independent_votes=0,
      scope='14 observers, three set outputs, one whole output on one identified model; written analytic links and finite verification stay separate.')
