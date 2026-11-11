# Float reference levels E0, E1, E2 of the two-square cell (theta graph) by Galerkin spin networks, K = 3, 4.
import json, pathlib, sys, time, numpy as np
HERE_ = pathlib.Path(__file__).resolve().parent
import sn_theta as sn
LAMS = [0, 0.1, 0.25, 0.5, 0.75, 1, 1.5, 2, 2.5, 3, 3.5, 4]
res = {}
for K in (3, 4):
    t = time.time(); n, herm, L = sn.levels(K, LAMS, k=3)
    res[K] = dict(states=n, herm=herm, levels=[list(map(float, x)) for x in L])
    print(f'K={K} states={n} hermiticity err={herm:.1e} ({time.time()-t:.0f}s)', flush=True)
print(' lam      E0(K=3)        E0(K=4)        E1(K=3)        E1(K=4)       gap(K=4)    dgap(K3-K4)')
for i, lam in enumerate(LAMS):
    a, b = res[3]['levels'][i], res[4]['levels'][i]
    print(f'{lam:5.2f} {a[0]:14.10f} {b[0]:14.10f} {a[1]:14.10f} {b[1]:14.10f} {b[1]-b[0]:12.8f} {(a[1]-a[0])-(b[1]-b[0]):+.2e}')
json.dump(dict(lams=LAMS, res=res), open(HERE_ / 'theta_reference.json', 'w'), indent=1)
