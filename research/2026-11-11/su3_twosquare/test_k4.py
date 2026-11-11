import numpy as np, theta_gt as tg, json
ref=json.load(open('/tmp/ymcount/research/2026-11-11/kyfan_chord/theta_reference.json'))
st,E,S,T=tg.build(1e4,K=4)
lams=ref['lams']; mx=0
for i,lam in enumerate(lams):
    L=tg.levels(E,S,lam,3); r=ref['res']['4']['levels'][i]; mx=max(mx,np.abs(L-np.array(r)).max())
print('K=4 states',len(E),'ref states',ref['res']['4']['states'],'max |dE| vs sn_theta K=4 over 12 lambdas, 3 levels:',mx)
