"""Exact P-block matrices from ham.build: G_PP, A_E = G E, A_B = G B_PP, C = B_QP^T G_QQ B_QP."""
from fractions import Fraction as F

def assemble(D):
    states, index, nP, Bcol, gram = D['states'], D['index'], D['nP'], D['Bcol'], D['gram']
    mod = D['model']
    # group state indices by configuration
    bycfg = {}
    for i, (c, idx) in enumerate(states): bycfg.setdefault(c, []).append(i)
    def gmul(col):
        """G times a sparse coordinate column (dict key->(F)) -> dict index->F."""
        out = {}
        for (c, idx), v in col.items():
            gb = gram[c]
            for i in bycfg[c]:
                g = gb.get((states[i][1], idx))
                if g: out[i] = out.get(i, F(0)) + g*v
        return out
    Gm = {}; AE = {}; AB = {}; Cm = {}
    for j in range(nP):
        c, idx = states[j]
        e = mod.energy(c)
        for i in bycfg[c]:
            g = gram[c].get((states[i][1], idx))
            if g:
                Gm[(i, j)] = g; AE[(i, j)] = g*e
        gb = gmul(Bcol[j])
        for i, v in gb.items():
            if i < nP: AB[(i, j)] = v
    # C_ij = <B b_i, Q B b_j> : Q-part of the columns
    qcols = []
    for j in range(nP):
        qcols.append({k: v for k, v in Bcol[j].items() if index[k] >= nP})
    gq = [gmul(qc) for qc in qcols]   # G_QQ applied (indices >= nP)
    # C = Bq^T (G Bq)
    byrow = {}
    for j, col in enumerate(gq):
        for i, v in col.items(): byrow.setdefault(i, []).append((j, v))
    for i, qc in enumerate(qcols):
        for key, bv in qc.items():
            r = index[key]
            for j, v in byrow.get(r, ()):
                Cm[(i, j)] = Cm.get((i, j), F(0)) + bv*v
    Cm = {k: v for k, v in Cm.items() if v}
    return dict(G=Gm, AE=AE, AB=AB, C=Cm, n=nP)

def check_symmetric(M):
    bad = [(k, v) for k, v in M.items() if M.get((k[1], k[0]), F(0)) != v]
    return len(bad)
