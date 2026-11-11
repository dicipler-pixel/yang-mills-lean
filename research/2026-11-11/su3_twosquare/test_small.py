import numpy as np, time, theta_gt as tg
# 1) 19-state cutoff: must reproduce the repo pencil (check_19.out: lam=1 E0,E1 = 5.79480995 10.7258532; lam=4 20.40829273 25.82337043)
st,E,S,T=tg.build(40/3+1e-9)
for lam in (0,0.1,1,4): print('ECUT=40/3',lam,tg.levels(E,S,lam,3))
# 2) arm cutoff K=3, no electric cutoff: must reproduce theta_reference K=3 (lam=1: 5.7947234090 10.7147437653; lam=4: 20.1448572549 25.3569811375)
st,E,S,T=tg.build(1e4,K=3)
for lam in (1,4): print('K=3',lam,tg.levels(E,S,lam,3))
