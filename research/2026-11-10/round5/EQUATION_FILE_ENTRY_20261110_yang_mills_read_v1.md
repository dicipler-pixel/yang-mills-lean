# Equation-file entry — 10 Nov 2026 — Yang–Mills full read and window wall (v1)

## Holds (checked today)
1. Window bound for the C<=8 complete-tail class (new, from LOCAL_ENERGY_FLOORS with s=0):
   d - r <= W(s) = s*(28/3) - Sum_p [ g(c_p,lam) - g((1-s) c_p, lam) ],
   W concave, W(0)=0, W'(0) = 28/3 - Sum_p c_p <C2>_p.
   If Sum_p c_p <C2>_p >= 28/3 no certificate of this class exists at any s.
   Check: all 58 stored targets obey it (smallest slack 0.000276); no stored target sits where W'(0) <= 0. Script WINDOW_WALL_01.
2. Small coupling: <C2> -> (3/8) lam^2 (measured ratio 0.389 at lam=1/20), so P_max ~ (224/9)/lam^2 faces at c_p=1.
3. interval_pivot_witnesses.json regenerates byte-identical (sha 1b8834e0...).
4. Two-plaquette true gap enclosures from the repo's own two-sided targets: lam 0.1 [5.284055, 5.284076]; 0.5 [5.102788, 5.103880]; 1 [4.908928, 4.931184]; 2 [4.273698, 4.811089]; 3 [2.466778, 5.226349]; 4 [0.991383, 7.019307].

## Set aside (kept, with the condition that failed)
- "Hidden-walk (Neumann) comparison closes hResolvedLeSchur": NOT needed for that purpose — RESOLVED_BOUNDARY.md already proves K_res <= S on paper (allocation D >= sC_Q+E_*, inverse order). Failure condition: it gives weaker numbers than the stored certificates (3.884 vs 5.648 at lam=10). Kept as a second, allocation-free route.
- "Outer bound W predicts where the search fails": it does NOT — double cube lam=1 has W'(0)=+6.22 yet the stored search was inconclusive. W only excludes; it does not locate the real edge.
- "At lam=4 the true two-plaquette E1 is above the hidden floor d": UNTESTED. Only the Ritz upper value (25.82) is above d (23.48).
- sqrt(lam)-oscillator lead for the single loop: UNTESTED in this round.
