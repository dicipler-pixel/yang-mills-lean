import sys; sys.argv=['cert.py','14']
src=open('cert.py').read().split("lam=F(5)")[0]; exec(src)
from fractions import Fraction as F
for mu in [F(10,7),F(5,3),F(500,301)]:
  up,wf=upper(mu); lo=lower(mu,wf)
  bad=F(round((wf+1e-3)*10**10),10**10)
  print('mu',mu,'lower',float(lo),'upper',float(up),'gap',float(up-lo),'| false z=E+1e-3 certified?',psd(mu,bad))
