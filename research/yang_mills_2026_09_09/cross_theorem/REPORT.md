# Yang–Mills: the boundary needs its energy labels

Research programme of Jeromie N. Beasley — 9 September 2026.

## Completed result

The actual Compound Eye now checks the same gauge model through geometry, boundary response, exact target relations, and spectral certificates. The useful light-paper connection is a positive energy-resolved boundary record: retain which energy belongs to each coupling contribution rather than dividing their entire Gram matrix by one worst-case denominator. This improves exact complete-tail certificates without enlarging the retained basis. The user's pinned Kakeya dual theorem has five explicit rational gauge instances, and safe positive-moment binning retains weaker certificates with fewer energy descriptors.

The final calculations cover five original-link SU(3) graphs, including a full cube and two adjacent cubes. They accept 58 primary rational targets. This is not a quantitative moderate-coupling infinite-volume gap, a derived continuum trajectory, or a four-dimensional quantum Yang–Mills construction.

## What was reused

The actual source reading includes Light Keeps the Ledger, research edition 3 (6 September), its positive transition-resolved optical weights and nullspace result; the supplied Elemental Peeling exact memory/hidden-initial-force discussion; the pinned KakeyaForcingLinear.lean source from PR #4; the boundary-support determinant-degree argument; and the prior Yang–Mills sources and certificates. Other historical definitions were inventoried for applicability, not falsely described as extra gauge runs.

The full downloadable native application preserves all 219 eye versions present at the start. It now has 241 eye versions and 48 set versions. This inventory includes revised combined outputs, not 22 independent discoveries. Each final model request executes 14 observers, three combined set outputs and one whole output: 90 outputs across five models. Three unchanged older UPG eyes also ran in 15 finite-compression contexts, producing 45 outputs. Shared computations are not independent votes.

The GitHub native/ directory is a focused deployment with the same unchanged machine.py; the full historical instrument, data and user-facing views travel in the user ZIP. These are different publication scopes.

## Analytic application chain

The missing TWO_PLAQUETTES.md and LOCAL_ENERGY_FLOORS.md have been reconstructed and committed. SCALING_AND_OBSTRUCTIONS.md is also reconstructed. The missing two-sided target data were regenerated and exactly accepted, not falsely described as recovery of the original bytes.

For the new graphs the complete physical electric cutoff is C<=8. Nontrivial SU(3) link representations cost at least4/3; the next Casimir is at least3. Gauss invariance forbids a degree-one occupied support. On the declared triangle-free, K2,3-free grid graphs, every possible admissible support with at most six edges is a single four- or six-cycle. The constant plus both fundamental orientations of every such cycle therefore give the complete C<=8 physical space. The entire omitted electric sector is at least28/3. The graph-specific finite support census supplements the all-irrep written argument; it is not substituted for it.

The two-adjacent-cube graph has12vertices,20links,11plaquettes and9independent graph cycles. Its60,459 occupied-edge supports of sizes1–6 were checked;11four-cycles and36six-cycles give95retained states. All matrices use original links and Haar/Fierz contractions. Six faces of a cube are not silently treated as six independent holonomies: its graph cycle rank is5.

Local allocation retains a fraction s of electric energy, divides the remaining electric terms among incident plaquettes, and sums certified local absolute ground-energy bounds e_p. This proves

    D >= s C_Q + E_* I,  E_* = sum_p e_p.

Overlapping local terms need not commute or share a ground vector. A local ground lower bound on the full cycle-link space extends by spectator identities. This is not a frustration-free decomposition or addition of local excitation gaps.

## The stronger boundary certificate

The earlier comparison already retains the full coupling Gram, rather than replacing it by a scalar norm. It uses

    K_floor(z)=A-zI-BB*/(d-z).

Let M_e>=0 be the exact electric-energy-resolved matrices, with BB*=lambda^2 sum_e M_e. Inverse order under the allocated full-sector lower bound yields

    K_res(z)=A-zI-lambda^2 sum_e M_e/(s e+E_*-z),
    K_floor <= K_res <= true Schur complement <= A-zI.

The condition z<d applies to the ENTIRE hidden space, including boundary-invisible states. A floor only on states reached by B* cannot replace it. The positive residues are a finite comparison measure, not the exact interacting D spectrum or its complete time-memory kernel.

Representative allocated lower bounds, alpha=1:

| Graph | Links | Faces | Complete retained dimension | lambda/alpha | One floor, full Gram | Energy-resolved |
|---|---:|---:|---:|---:|---:|---:|
| Two squares | 7 | 2 | 7 | 1 | 4.388047 | 4.696420 |
| Three-square strip | 10 | 3 | 11 | 1 | 3.912389 | 4.366060 |
| Three-face corner | 9 | 3 | 15 | 1 | 3.817251 | 4.280636 |
| Full cube | 12 | 6 | 45 | 1 | 1.649349 | 2.109917 |
| Two adjacent cubes | 20 | 11 | 95 | 1/2 | 3.295750 | 3.817691 |

These are lower bounds, not exact gaps or masses in physical particle units. The seven-state first row isolates the improvement; it is not advertised as stronger than the earlier 19-state two-square bound4.908928.

A stricter paired control freezes the graph, basis, s, all local floors, r and z at each resolved target. The old lower comparison matrices have respectively3,4,4,31,23negative directions; the resolved ones have exactly1. These are comparison-matrix inertias, not numbers of physical negative states. This isolates the energy-label improvement at identical parameters.

The fresh four-model grid has52accepted targets, plus6on two cubes, for58. An earlier reported54-target file was not recovered; it is not substituted into this count. At lambda/alpha=1, the tested95-state two-cube allocation grid is inconclusive, not gapless.

## Safe coarsening, not averaging before inversion

For a bin a<=e<=b and t=E_*-z, set x=se+t, x_a=sa+t, x_b=sb+t>0. Then

    (x_a+x_b-x)/(x_a x_b)-1/x
      =(x-x_a)(x_b-x)/(x_a x_b x)>=0.

This gives an upper penalty from two moments M0=sum M_e and M1=sum e M_e per bin. Positive matrix summation needs no commutativity of the residues. The binned penalty lies between the resolved and whole-floor penalties.

Three bins/six moments replace the cube's eleven residues and certify gap>=2 at lambda/alpha=1. Two bins/four moments certify gap>=7/2 on two cubes at lambda/alpha=1/2. The parent resolved bounds2.109917 and3.817691 are stronger. At these binned test points the one-floor negative counts are14and2; the binned count is1each. These are two additional weaker comparisons, not two extra primary model targets.

The current code constructs residues before binning; fewer descriptors is not a demonstrated speedup. A mean-energy substitution is unsafe: 1/10+1/14=6/35 exceeds2/12=1/6, so that substitution underestimates the penalty. The native coarsening eye retains the required one-sided inequality.

The boundary-support rank argument also yields sufficient comparison-determinant pole degrees259rather than495for the cube and674rather than1045for two cubes. These are sufficient algebraic bounds, not sharp physical eigenvalue counts.

## A direct gauge instance of the actual Kakeya theorem

The pinned source is OperatorFirst/KakeyaForcingLinear.lean at41fbf3b9e6ad8143d597928e477a9d94adb6d6d6. Its CanForce(T,b) means an invisible vector exists: Tx=0 but bx!=0. The dual_certificate theorem excludes CanForce when b=y composed with T. Reversing that implication would reverse the meaning of the test.

For the actual gauge matrices at lambda/alpha=1, ker M is span(e0), where e0 is the constant ELECTRIC vacuum vector. Thus b(x)=x0 is invisible to M alone. Stack Theta x=(Mx,MAx). Exact rational rows satisfy

    y0 M+y1 M A=e0^T.

The five new gauge instances check173scalar equalities (7+11+15+45+95) and reject five damaged dual rows. The source theorem therefore excludes a hidden change of this target under the stacked observation. The same positive-Gram calculation gives rank(M)=n-1 and rank(M+AMA)=n.

This is a concrete application with a named target and witness, not rank-only analogy. It is retained-generator algebra, not an uncontrolled measured time derivative with unknown hidden forcing. It does not prove observability of every state in the infinite hidden Hilbert space. The old general Lean theorem is pinned; the173new numerical identities are exact Python checks, not a new Lean module.

## Independent checks and actual native reproduction

Independent original-link Gell-Mann differentiation, physical gauge transformations and60,000 full-link Haar configurations pass35,602 numerical diagnostic assertions. The vertex-only two-square control has exactly zero shared-link kinetic cross term; merely sharing a vertex does not automatically supply the interaction suggested in the pasted review.

The three unchanged earlier UPG eyes—redistribution memory, spectral susceptibility and logdet gluing—were run on15finite compressions. Their45outputs and61checks retain PHP as their domain; a finite ground-projector derivative was separately checked by finite differences. None is labeled a measurement of the full physical vacuum.

The full native integration passes366assertions including six malformed-input controls. Its final five-model run produces90outputs. The release entry point was also run with optional numerical checks: native_full, focused_reproduction, independent_spatial and inherited_compression all exit0. Output paths are isolated and earlier evidence is not overwritten.

[Native CI run34412059750](https://github.com/dicipler-pixel/operator-first/actions/runs/34412059750), source0cfcc41ebe74efe8040cd50645c87c8b0d11a55f, rebuilds all five original-link matrix records and reaccepts58targets with no eigensolver. Its artifact SHA256 is d0b24a79e38cc564f31c1d3f205bb5fc3a484ccdff3bc8d5c35bd1cb9a6b73d4. All104manifest hashes and all six delivered deployment sources match. Four false-premise controls fail as required.

[Lean run34407919722](https://github.com/dicipler-pixel/operator-first/actions/runs/34407919722), sourcef7f14139a8f101cc49b6d98885eae2341235e739, accepts12closing declarations. CrossTheorem.lean hash17b24ca14adc668e58aaa71c5207580a5ade66f3214b30c71a01cbd09487b1d3matches the artifact. Allowed axioms are propext, Classical.choice, Quot.sound; the false inequality is rejected after valid imports. These are scalar denominator/weight/error and conditional gap-closing steps, plus cube arithmetic. They do not formalize Haar, complete spin-network bases, infinite-dimensional Schur/min-max, the whole spectral-window operator proof, or continuum existence. No separate Leanchecker replay was done. Declaration inventories are not summed with old21or elemental71as new discoveries.

Fraction parsing failures, interrupted bounded attempts and the prose173count correction remain in the evidence. No failed experiment is silently relabeled a success.

## Correct spatial-uniformity distinction and current sources

The proof FIXED_COUPLING_STABILITY_MAP.md applies Yarotsky's established Theorem1, including its infinite-dimensional on-site hypotheses, to a fixed-spacing sufficiently-small-lambda/alpha regime. A four-site classical patch has a unique normalized ground state and gap>=1; the centered plaquette perturbation is bounded by81(lambda/alpha)/4. For sufficiently small fixed ratio the cited theorem gives a volume-independent gap. The physical invariant restriction keeps the unique ground state and cannot lower that gap.

No numerical threshold is obtained, so this does not admit lambda/alpha=1 or prove quantitative uniformity for the displayed moderate-coupling table. This is established stability theory applied with explicit hypotheses, not a new theorem credited to this programme.

The fixed-cell gap certificates extend by bounded perturbation to intervals: cube lambda/alpha in[0.95,1.05] gives gap>=0.759917alpha; two cubes in[0.45,0.55] gives>=1.342691alpha. They are not renormalization trajectories.

Primary comparisons checked include Yarotsky math-ph/0412040v1; Balaji et al. PRD113,094505(2026),doi10.1103/m719-7tdf, which already studies an SU3cube; Li et al. arXiv2608.27267(August2026)on maximal-tree gauge; Yang,Kane,Jabeen arXiv2604.24896v4 on energy-based truncation; and Tong et al. arXiv2110.06942. There is no first-cube, exhaustive-literature or historical-priority claim.

The review's advice to supply missing proofs, keep units consistent and avoid frustration-free substitution is useful. A large-grid window error must be compared only with the gap of the SAME operator and cutoff, not a borrowed two-plaquette margin. A complete-tail total-electric Schur certificate does not require a second product-link-window error subtraction. Exact Casimir floors cannot be arbitrarily raised. Every finite graph used here is explicitly open-boundary, not an unnoticed degenerate periodic torus.

## Reproduce and continue

From cross_theorem/native run `python -S recheck.py --out fresh_evidence`. It builds a new focused native registry, reconstructs the five exact matrices and accepts all58targets. Existing output directories are refused. The full user bundle supplies RECHECK.py and the preserved full historical instrument, optional independent numerical tests, offline dashboard, report PDF, source ledger and all output/receipt files.

The next quantitative task is a useful comparison under growth in spatial volume, with consistent normalization and without losing the interacting vacuum. Direct positive-moment construction and a quantitative stability estimate are specific possible steps; the current finite-cell table and observability witnesses are not that proof.

Main and the Earth–Moon hard-backup branch remain unchanged. The frozen backup still hashes to e11c2770f6a80badbf2c661f27605e99a3001d56b1d4a629e9a23d934fcdfa80. No process is promised after this session. The result is a concrete cross-theorem improvement and an executable gauge-observation test, not a claim to have completed quantum Yang–Mills.
