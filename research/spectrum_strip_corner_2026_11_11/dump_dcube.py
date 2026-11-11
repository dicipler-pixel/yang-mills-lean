# Build the exact double-cube retained data (95 = 1 + 2*(11 squares + 36 hexagons)) with the repo's
# spatial_gauge.calculate and cache S (and M) as exact rationals in dcube_S.json.
import sys, os, json, time
from pathlib import Path
from fractions import Fraction as F
HERE = Path(__file__).resolve().parent
YM = os.environ.get('YM_RESEARCH', str(HERE.parents[1] / 'research' / 'yang_mills_2026_09_09'))
for p in ('/scripts', '/cross_theorem/scripts', '/cross_theorem/native'): sys.path.insert(0, YM + p)
import spatial_gauge as sg
t = time.time()
m, d = sg.calculate('double_cube')
n = len(m['energies'])
print('dimension', n, 'faces', len(m['faces']), 'edges', len(m['edges']), 'seconds', round(time.time() - t, 1))
json.dump(dict(n=n, P=len(m['faces']), energies=[str(e) for e in m['energies']], names=m['basis_names'],
               S=[[str(x) for x in r] for r in d['S']], M=[[str(x) for x in r] for r in d['M']],
               shells=[str(e) for e in d['masses']]), open(HERE / 'dcube_S.json', 'w'))
