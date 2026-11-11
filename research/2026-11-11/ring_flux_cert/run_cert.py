"""Driver: python run_cert.py L cap0 cap1  -> ring_L{L}.json / .out"""
import sys, json, time
from fractions import Fraction as F
import numpy as np, scipy.linalg as sl
import su3rep as S, ring, ham, matrices, cert

def fr(x): return None if x is None else (str(x) if isinstance(x, F) else x)

def main():
    L = int(sys.argv[1]); caps = {0: F(sys.argv[2]), 1: F(sys.argv[3])}
    lams = [F(1, 4), F(1, 2), F(1)]
    G = ring.ring_graph(L)
    out = dict(L=L, caps={k: str(v) for k, v in caps.items()}, results={})
    log = open(f'ring_L{L}.out', 'w')
    def P(*a):
        s = ' '.join(str(x) for x in a); print(s, flush=True); log.write(s + '\n'); log.flush()
    P(f'# SU(3) periodic ring L={L}: H = sum C2 + lam sum_p (3 - Re tr U_p), units g^2/2')
    data = {}
    for sec in (0, 1):
        t = time.time()
        D = ham.build(G, sec, caps[sec])
        # basis completeness cross-check: intertwiner counts vs independent character multiplicities
        mod = D['model']
        for c in D['Pcfg'] + D['Qcfg']:
            for v in mod.vorder:
                legs = mod.legs(c, v)
                assert len(S.vertex_invariants(legs)) == ring.inv_dim(legs)
        Mx = matrices.assemble(D); n = Mx['n']
        sym = (matrices.check_symmetric(Mx['AB']), matrices.check_symmetric(Mx['G']), matrices.check_symmetric(Mx['C']))
        Mf = tuple(cert.dense(Mx[k], n) for k in ('G', 'AE', 'AB', 'C'))
        minE = min(mod.energy(c) for c in D['Pcfg'])
        P(f'sector {sec}: cap {caps[sec]}, P = {len(D["Pcfg"])} configs / {n} states, Q1 = {len(D["Qcfg"])} configs / '
          f'{len(D["states"])-n} states, exact symmetry defects (AB,G,C) = {sym}, min electric energy in sector = {minE}, build {time.time()-t:.0f}s')
        assert sym == (0, 0, 0)
        data[sec] = (D, Mx, Mf, minE)
    for lam in lams:
        res = {}
        P(f'\n## lam = {lam}')
        for sec in (0, 1):
            D, Mx, Mf, minE = data[sec]
            hf = cert.hidden_floor(G, sec, caps[sec], lam)
            P(f' sector {sec} hidden floor: d = {hf["d"]} = {float(hf["d"]):.5f}  (theta={hf["theta"]}, m_Q={hf["mQ"]}, '
              f'min E on Q = {hf["minE_Q"]}, local e0({hf["mu"]}) >= {hf["e0_lo"]} [float {hf["e0_float"]:.6f}; +1/1000 rejected: {hf["e0_ctrl_count"]>=1}])')
            r = dict(hidden=hf)
            r['E0_up'], r['E0_float'] = cert.rayleigh(Mx, Mf, float(lam), 0)
            P(f'   RR: E0 <= {float(r["E0_up"]):.8f} (exact rational; float eig {r["E0_float"]:.8f})')
            for k in ((0, 1) if sec == 0 else (0,)):
                c = cert.certify_level(Mx, Mf, lam, hf['d'], k)
                r[f'E{k}_lo'] = c
                if c['ok']:
                    P(f'   E{k} >= {c["z"]} = {float(c["z"]):.6f}  (#neg K = {c["count"]} <= {k}, disc margin {c["margin"]:.2e}; '
                      f'float threshold {c["zf"]:.6f}; control z+1/1000: count {c["ctrl_count"]} rejected={c["ctrl_rejected"]})')
                else:
                    P(f'   E{k}: NOT certified ({c.get("reason")})')
            w = sl.eigh(Mf[1] + float(lam)*Mf[2], Mf[0], eigvals_only=True)[:3]
            r['float_levels_P'] = [float(x) for x in w]
            P(f'   float levels in P: {w}')
            res[sec] = r
        s0, s1 = res[0], res[1]
        summ = {}
        if s0['E1_lo']['ok']:
            summ['gap_lo'] = s0['E1_lo']['z'] - s0['E0_up']
        if s1['E0_lo']['ok']:
            summ['floor_lo'] = s1['E0_lo']['z'] - s0['E0_up']
        if s0['E0_lo']['ok']:
            summ['floor_up'] = s1['E0_up'] - s0['E0_lo']['z']
        summ['gap_float'] = s0['float_levels_P'][1] - s0['float_levels_P'][0]
        summ['floor_float'] = s1['float_levels_P'][0] - s0['float_levels_P'][0]
        P(' SUMMARY: ' + ', '.join(f'{k} = {float(v):.6f}' for k, v in summ.items()))
        out['results'][str(lam)] = dict(summary={k: [str(v), float(v)] for k, v in summ.items()},
            sectors={sec: dict(E0_up=[str(r['E0_up']), float(r['E0_up'])], E0_float=r['E0_float'],
                               float_levels_P=r['float_levels_P'],
                               hidden={k: fr(v) for k, v in r['hidden'].items()},
                               **{key: {kk: fr(vv) for kk, vv in r[key].items()} for key in r if key.endswith('_lo')})
                     for sec, r in res.items()})
    json.dump(out, open(f'ring_L{L}.json', 'w'), indent=1, default=str)

if __name__ == '__main__':
    main()
