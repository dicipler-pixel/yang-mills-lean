# Auditor report — four claims, recomputed independently

Repo read: dicipler-pixel/yang-mills-lean at ff9c203 (documents only; no repo Python imported, called or copied).
Scripts: `audit_a1.py`, `audit_a2.py`, `audit_a3.py`, `audit_a4.py`, each run as `python3 -I <file>` from `/`. All four exit 0.

| Target | Verdict |
|---|---|
| A1 two-square electric table through 40/3, next level 43/3 | SURVIVES |
| A2 complete C<=8 bases 7, 11, 15, 45, 95 and floor 28/3 (all five graphs, two-cube run completed) | SURVIVES |
| A3 even-split plaquette coefficients | SURVIVES |
| A4 allocation inequality sanity check on two squares | SURVIVES (necessary-condition test only) |

No discrepancy with any claimed number was found. The points under "Document remarks" are gaps or ambiguities in the written text, not numerical failures.

## A1 — theta graph (1,3,3)

Computed: SU(3) tensor multiplicities by my own routine (weights from Gelfand–Tsetlin patterns, then Racah–Speiser reflection with the A2 Weyl group). Self-test: sum N_a dim(a) = dim(b) dim(c) and commutativity on all 2401 pairs with p,q <= 6; 3x3 = 6 + 3bar, 3x3bar = 1 + 8, 8x8 = 1+8+8+10+10bar+27 all reproduced. Then every (a,b,c) with c(a)+3c(b)+3c(c) <= 15, n = multiplicity of a* in b x c, physical multiplicity n^2, exact Fractions. Irreps with p or q up to 8 were scanned; c(9,0) = 36 > 15, so nothing is cut.

| Energy | New | Cumulative | Claimed cumulative |
|---:|---:|---:|---:|
| 0 | 1 | 1 | 1 |
| 16/3 | 4 | 5 | 5 |
| 8 | 2 | 7 | 7 |
| 28/3 | 2 | 9 | 9 |
| 11 | 2 | 11 | 11 |
| 34/3 | 2 | 13 | 13 |
| 12 | 2 | 15 | 15 |
| 40/3 | 4 | 19 | 19 |
| 43/3 | 4 | 23 | (next level, claimed 43/3) |

No level in (40/3, 43/3), and 43/3 is the only further level <= 15. Every multiplicity through 43/3 is 1. The 43/3 level holds 4 states (long adjoint + long fundamental + short fundamental, both orientations and both arm choices).

Final lines:
```
largest intertwiner multiplicity through 40/3: 1
next level above 40/3: 43/3 with 4 states
RESULT A1: SURVIVES
```

## A2 — five graphs, C <= 8 and the 28/3 floor

Graphs built from their descriptions: 3x2 grid, 4x2 grid, cube minus vertex 111 (binary labels 0..6, Hamming distance 1), 2x2x2 grid, 3x2x2 grid.

Cycle counts by my own depth-first enumeration:

| Graph | Vertices | Links | 4-cycles | 6-cycles | 1 + 2(c4+c6) | Claimed |
|---|---:|---:|---:|---:|---:|---:|
| Two squares | 6 | 7 | 2 | 1 | 7 | 7 |
| Three-square strip | 8 | 10 | 3 | 2 | 11 | 11 |
| Three-face corner | 7 | 9 | 3 | 4 | 15 | 15 |
| Cube | 8 | 12 | 6 | 16 | 45 | 45 |
| Two adjacent cubes | 12 | 20 | 11 | 36 | 95 | 95 |

Floor test, done as an exhaustive labelling enumeration rather than a support count: every edge subset of size 1..7 (8 links already cost 32/3), kept if every occupied vertex has occupied degree >= 2; then every labelling of the kept subsets by the irreps of Casimir <= 16/3, namely 3, 3bar, 8, 6, 6bar, (2,1), (1,2) — two more than the task asked for, so the label set is provably complete for C <= 28/3 (a link above 16/3 plus the three further links any admissible support needs exceeds 28/3). Each vertex is tested with the true dimension of the invariant space of the incident irreps (duals taken on incoming links), including the 4-valent vertices of the two-cube graph; a labelling's state count is the product of those dimensions.

| Graph | Subsets examined | Min-degree >= 2 | States at 0 | 16/3 | 8 | 28/3 | Anything in (8, 28/3) | C<=8 dimension |
|---|---:|---:|---:|---:|---:|---:|---|---:|
| Two squares | 127 | 4 | 1 | 4 | 2 | 2 | none | 7 |
| Three-square strip | 967 | 7 | 1 | 6 | 4 | 4 | none | 11 |
| Three-face corner | 501 | 10 | 1 | 6 | 8 | 6 | none | 15 |
| Cube | 3301 | 34 | 1 | 12 | 32 | 24 | none | 45 |
| Two adjacent cubes | 137979 | 75 | 1 | 22 | 72 | 56 | none | 95 |

The only energies <= 28/3 are 0, 16/3, 8, 28/3 on every graph. Every admissible labelling with C <= 8 is the constant or a single 4- or 6-cycle carrying 3 or 3bar with multiplicity 1. The floor 28/3 is attained on all five graphs (two fundamental baryon-type states on each theta subgraph of 7 links: 1, 2, 3, 12, 28 such subgraphs). The two-cube case finished in under a second after pruning, so nothing is left incomplete. The two-square row agrees with A1 by a different route (product of vertex invariants instead of n^2).

Final lines:
```
       28/3 : 56 (56)
    physical dimension with C <= 8: 95  claimed 95
    elapsed 0.4 s
RESULT A2: SURVIVES
```

## A3 — even-split coefficients

Exact Fractions, c_p = sum over the four links of 1/(plaquettes on that link):

| Graph | c_p | Sum | Average |
|---|---|---:|---:|
| Two squares | 7/2, 7/2 | 7 | 7/2 |
| Three-square strip | 7/2, 3, 7/2 (3 is the middle face) | 10 | 10/3 |
| Three-face corner | 3, 3, 3 | 9 | 3 |
| Cube | 2 x 6 | 12 | 2 |
| Two adjacent cubes | 11/6 x 8, 2 x 2, 4/3 x 1 | 20 | 20/11 |

Final lines:
```
two adjacent cubes   links 20 faces 11  c_p = ['11/6', '11/6', '2', '11/6', '11/6', '11/6', '11/6', '4/3', '11/6', '11/6', '2']  sum = 20  average = 20/11
                     plaquettes-per-link histogram: {2: 16, 3: 4}
RESULT A3: SURVIVES
```

## A4 — allocation inequality, two squares, lambda = alpha = 1

I did not build the full (a,b,c) spin-network Hamiltonian (it needs SU(3) 6j recoupling coefficients, which I could not derive and validate from first principles in the time). I did the simpler check, plus one extra that uses no repo number.

- One-plaquette model in the character basis, kappa = 7/2, lambda = 1: g = 2.881304425230 at cutoffs p+q <= 10, 20, 40, 60 (identical to 12 decimals; 1891 states at 60). First excited level 7.161579116109.
- 2 g(7/2) = 5.762608850459.
- Repo E0 (README table, ECUT 250) = 5.794723397655. Margin 0.032114547196 >= 0: kill condition not met.
- Extra, repo-independent: my own seven-state Rayleigh–Ritz matrix in the basis 1, TrU, TrU*, TrV, TrV*, Tr(UV*), Tr(VU*) (matrix elements derived by hand from Haar integrals, spot-checked by seeded Haar Monte Carlo, max deviation 0.0031 on the Gram and 0.0102 on the multiplication matrix at 400,000 samples) gives E0 <= 5.801016446939. So 5.762609 <= 5.794723 <= 5.801016: the repo value sits inside a bracket I built without it.
- Trivial consistency only: certified gap lower bound 4.908928 < reported reference gap 4.920018775899. I did not recompute either number.

Final lines:
```
repo E0 (ECUT 250)    = 5.794723397655   margin = 0.032114547196
own 7-state upper bound on E0 = 5.801016446939   (Monte Carlo check of my Gram / S matrices: max dev 0.0031 / 0.0102)
own 7-state E1 = 10.833333333333, 7-state gap = 5.032316886394 (Galerkin value, not a bound on the gap)
RESULT A4: SURVIVES
```

## Document remarks (numbers right, text thin or ambiguous)

1. SPATIAL_BASES.md says "All five declared graphs" but its definition table lists four. The two-adjacent-cube graph is described only in REPORT.md, by counts (12 vertices, 20 links, 11 plaquettes). I took it to be the 3x2x2 grid (two cubes sharing a face); that reproduces every count, but the document never writes its edge list.
2. LOCAL_ENERGY_FLOORS.md lists coefficients for four graphs only. The two-cube value 20/11 appears in other files (window_wall, spectrum_dictionary) as a uniform split. It is the average of the even split, not the even split itself: the even-split values are 11/6 (eight faces), 2 (two end faces) and 4/3 (shared middle face). Any text that uses 20/11 on every face is using a different allocation from the one LOCAL_ENERGY_FLOORS.md defines, and needs its own feasibility statement (the repo's dictionary notes mention one; I did not check it).
3. TWO_PLAQUETTES.md states the 43/3 floor is attained and gives one example; the level has 4 states. Not an error, just not stated.
4. TWO_PLAQUETTES.md takes "physical multiplicity n^2" as given. It is correct here (my A2 route computes the product of the two vertex invariant dimensions and agrees), but the document does not say that n(a,b,c) = n(a*,b*,c*) is what makes the product a square.
5. The support theorem in SPATIAL_BASES.md treats a support as a subgraph and bounds energy by link count. It never states the multiplicity of a labelling at vertices of valence 3 or 4 where only two links are occupied (it is 1), nor that a support of 7 or more links can carry more than one state. Neither affects C <= 8; my enumeration covers both.
6. A4 is a necessary-condition test. The README's E0 is a truncated Galerkin value, an upper bound on the true E0, so passing does not prove H >= h_1 + h_2. The positivity-improving / unique-ground-state step in LOCAL_ENERGY_FLOORS.md is cited from standard theory and was not audited.

## Not audited

The 19-state gap certificate 4.908928 itself, the norms 4/3, 8/3, 8/9 of the extended trace basis, the Schur-complement formulas, the float reference gap 4.920018775899, and everything in kyfan_chord were not recomputed.
