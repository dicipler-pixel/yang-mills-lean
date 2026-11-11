# Read record 11 — yang-mills-lean (commit 0b627d8, main, 1 Nov 2026), read 10 Nov 2026

113 files. Each entry: file, read in full or not, what it states.

## Batch 1 — top-level documents (all read in full)
- README.md: 80 theorems in 14 modules. One-line idea: keep the SHAPE of the coupling to the discarded sector (a boundary matrix), not its norm. Single-loop SU(3) certificate plus five original-link spatial models with 58 rational targets. No 4D continuum gap claimed. CI: build, kernel replay, axiom audit, two false controls.
- LIMITATIONS.md: NOT supplied: physical local-floor hypotheses; the local-allocation operator inequality; RG/polymer activity estimate; volume uniformity, thermodynamic or continuum limit; OS reconstruction; Clay theorem. Formal assembly of the physical Schur matrix + LDL witness into the quadratic-form hypotheses, and the infinite self-adjoint operator, remain formalization tasks. Holonomy audit DISPROVES a proposed universal first-order response statement. Small-coupling stability application is qualitative only.
- PRIOR_ART_AND_SCOPE.md: Schur/Feshbach framework credited to prior work (Dusson-Sigal-Stamm; Ciavarella et al.). At lambda/kappa=100 the scalar-norm estimate gives -33.3376 (inconclusive); the boundary-matrix one gives 1936077/100000.
- PROVENANCE.md: 12 Lean files copied from private operator-first at 3eb82d5f5dd5; two Schur-inertia modules new here; paper/2026-09-08 from a verified zip; research/ from private PR #18. Lean under research/ is historical, not built.
- SCHUR_INERTIA_BRIDGE.md: H=[[A,B],[B+,D]], D>=dI, S(z)=A-z-B(D-z)^-1 B+. If K(z)<=S(z)<=A-z and K has exactly one negative pivot, H has one simple eigenvalue below z. Complete-tail: K_M=A-z-M/(d-z). Spatial: K_res(z)=A-z-lambda^2 Sum_e M_e/(s e+E*-z), needs the FULL hidden floor D>=s C_Q+E* I, "including states invisible to B+".
- scripts/config.json: module list, expected_theorems 80.

## Batch 1 — LongestYangMillsChain.lean (read in full; 7 theorems)
1 commutator_zero_implies_memory_zero; 2 commutator_zero_implies_schur_reduces; 3 transport_metric_memory_chain (tangent of transported projector = commutator; half cross energy = trace of feedback Gram = coupling energy); 4 resolved_penalty_preserves_retained_floor; 5 resolved_schur_chain_to_full_floor — LOAD-BEARING HYPOTHESIS hResolvedLeSchur: K_res <= S is ASSUMED, not proved; 6 allocation_overlap_tail_chain (scalar bookkeeping: local floors, overlap capacity <=1, tail budgets, positive residual); 7 dual_certificate_survives_presentation.

## Batch 2 — seven Lean modules (all read in full)
- CrossTheorem.lean (12): scalar closing steps. denominator_positive; resolved_term_le and resolved_sum_le (energy-resolved denominators beat a common floor); shared_shift_does_not_improve_floor ((d-c)-(r-c)=d-r); window error (omega S+K)/(1-S); gap_transfer_closing_step: min(omega, mu1-mu0-error) <= E1-E0. Cube constants: 2(1-13/20)=7/10; (13/20)(28/3)+6(92681/40000)=1198129/60000; 8720479/500000 < 156407/8000 < 1198129/60000; margin 2109917/1000000. Header: does NOT formalize Peter-Weyl, Haar, Schur inertia, the infinite local-window argument, or the 45-state cube matrices.
- MatrixResolvedBoundary.lean (5): resolvedMatrixPenalty = Sum (1/(s e_i+offset-z)) M_i <= commonFloorMatrixPenalty in PSD order, for PSD M_i.
- SchurCongruence.lean (3): finite block congruence to diag(Schur complement, D); elimination matrix invertible.
- ProjectorKernel.lean (3): P=QA with AQ=1 is idempotent, fixes the frame, complement kills it.
- CouplingFeedback.lean (4): redistribution and zero-time feedback Gram B B^T vanish iff B=0; factorized feedback.
- ObservabilityKernel.lean (3): CanForce iff ker A not inside ker b; dual certificate rules it out; invariant under change of presentation.
- ProjectorDynamics.lean (7): [H,P] = [[0,-B],[B^T,0]]; zero iff B=0; trace of feedback Gram = coupling energy = half the projector cross energy; transported projector U P V has tangent [K,P] (derivatives are hypotheses, no exponential).

## Batch 3 — remaining root Lean (all read in full)
- GaugeCertificates.lean (21): exact rational LDL^T for the two-plaquette SHARED-LINK SU(3) certificate: inner 10x10 (all pivots positive), outer 7x7 (first pivot -4, the other six positive). Constants: (7/2)(1-17/20)=21/40; 1/(21/40)=40/21; (21/10)/(21/40)=4; 4<8; hidden floor (17/20)(28/3)+2(21/10)=182/15; test energies 6<10<182/15; tail denominator 32/15; margin 10-6=4; shared rectangle electric 6(4/3)=8; "independent_rectangle_is_wrong" 8(4/3)!=8; first baryonic tail 7(4/3)=28/3. Header: does NOT formalize Haar, basis completeness, analytic tail, Sylvester inertia.
- TailGapTransfer.lean (6): one-sided nonuniform tail budgets; (delta - Sum eps) scale <= base - Sum tail; overlap-aware ledger (no disjointness).
- SchurFloorTransfer.lean (3): full shifted block PSD iff Schur complement PSD when hidden shifted block is PD.
- NonuniformAllocationFloor.lean (3): local floors with allocation capacity <=1 per energy term sum to a global floor.
- SchurInertiaComparison.lean (2): K<=S carries a positive subspace; S<=A carries a negative trial vector.
- SchurInertiaCount.lean (1): positive on codimension one + negative on dimension one => exactly one negative direction, radical zero.
- FalseControls/ (2 files): (2:Q)=3 and 1/2<=1/3 must fail.
Count check: 12+5+3+3+4+3+7+21+6+3+3+7+2+1 = 80. Matches README.

## Batch 4 — scripts/verify.py (head read: audit logic), paper/2026-09-08/README.md, YANG_MILLS_CONTINUATION.md (read in full)
Paper "Retained Geometry and Certified Gauge Cutoffs", 8 Sept 2026.
- §2 Prop 1: for A=c U^+dU, Tr(F^F)=0 pointwise; the equal-weight graph frame (c=1/2) cannot carry second Chern density. §2.1 variable weight Q_t recovers the BPST instanton, Tr(F^F)=48 rho^4/(rho^2+r^2)^4, integral 8 pi^2, charge -1 (established; reconstructed).
- §3 Thm 2: explicit 195x3 frame Q with Q^+Q=I, Q^+dQ=A for any bounded C^2 local SU(3) connection (instance of universal connections; no optimality).
- §4 Schur with domain; §4.1 scalar estimate E1 >= (mu1+d-sqrt((d-mu1)^2+4b^2))/2; §4.2 Thm 3: K_M(z)=A-z-M/(d-z), BB^+<=M, one negative + (m-1) positive => exactly one eigenvalue below z; gap >= z-r.
- §5 gauge-compatible electric cutoff P_R=1_[0,R](C); D_R>=alpha c_+(R); B_R B_R^+ = P V^2 P-(PVP)^2; at fixed lattice the certificate converges to the true gap (completeness, not uniform).
- §6 one-plaquette SU(3): H=kappa C2+lambda(3-Re chi_10), six-neighbour fusion, d_N formula, only shell p+q=N couples out; BB^+ on that shell has diagonal lambda^2/2, adjacent lambda^2/4. Table: lambda 0: 4/3 exactly (N=1); 0.1: 1.2868372 (N=3, dim 10); 1: 1.3401688 (N=6, dim 28); 10: 5.6481431 (N=10, dim 66); 100: 19.3607700 (N=25, dim 351). Scalar certificate at 100: -33.33761265. 20 inertia certificates, 2,275 pivot signs, 13,587 assertions, 2^-192 grid.
- §7 audit: the proposed universal discrete-wall holonomy theorem is too strong; Tr W(a,b)=3-4 sin^2(a/2) sin^2(b/2) varies with no wall; nonzero symmetry-breaking tangent can have zero linear response; APS eta is real-valued, not an integer signature. Table of retained objects and what each still needs.
- §9 open: dependence on number of links/plaquettes, volume, spacing, coupling trajectory. Next uniform target stated: r<z<d per lattice with z-r>=Delta*>0. Multiscale: Delta_{j+1}>=(1-eta_j)Delta_j positive iff Sum eta_j<infinity.

## Batch 5 — paper tail + gap_review/GAUGE_CUTOFF_GAP_THEOREM.md (read in full)
- §1 congruence H-z = L^+ diag(S(z), D-z) L; n_-(H-z)=n_-(S(z)); at most m eigenvalues below d; essential spectrum edge >= d.
- §2 closed-form L (eq 5), sharp on A=diag(0,3), D=6, B=(0,2)^T (eigs 0,2,7; L=2). Positive iff b^2 < (mu1-mu0)(d-mu0). If L<=mu0 the bound is inconclusive, NOT gap closure.
- §3 K_M certificate; W^+ K_M W > 0 with exact LDL as the finite certificate; external bounds D>=d and BB^+<=M are proof obligations (floats not enough).
- §4 full finite lattice: H=alpha C + V_B, 0<=V_B<=M_B=6 Sum kappa_p (9/2 sharper), ||B_R|| <= M_B/2, D_R >= alpha c_+(R).
- §5 fixed lattice: certificate converges to true gap as R->inf; NOT uniform in links/plaquettes/volume/spacing; M_B grows with plaquette count.
- §6 product criterion iff Sum eta_j < inf (for the certificate only; eta=1/2, Delta=1 counterexample shows loose bound != closure); with rescaling a_j need inf Sum[log a_j + log(1-eta_j)] > -inf; limit operator needs strong resolvent convergence + vacuum projector convergence.
- §7 195x3 frame audit: weights w0=1/2, w+-=delta +- a/(2K), 65 blocks.

## Batch 6 — scripts/verify.py (rest, read in full), .github/workflows/build.yml, su3/SU3_SINGLE_LOOP_CERTIFICATE.md (read in full)
- verify.py: theorem inventory must equal expected count; `#print axioms` on every theorem, anything outside the allowed set fails; every FalseControls file must be REJECTED for a mathematical reason (not infra).
- CI: build, leanchecker replay per module, verify.py, evidence artifact.
- SU3 doc: "No Lean verification was run for this module" (the numerical certificate is Python exact-interval, 2^-192, not Lean). ||B|| = lambda cos(pi/(2N+4)); certificates use b=lambda. BB* tridiagonal (2,1) x lambda^2/4 on outer shell only.
- Tables: scalar bounds 4/3, 1.2852796, 1.2758093, 2.0814038, -33.3376127; boundary 4/3, 1.2868372, 1.3401688, 5.6481431, 19.3607700. mu0/mu1 enclosures: 0.1: [0.2961080,..85],[1.5829461,..66], E1>=1.5829457; 1: [2.5198544..],[3.8600240..], 3.8600237; 10: [11.2158942..],[16.8641367..], 16.8640378; 100: [38.5784689..],[57.9392397..], 57.9392394.
- Limits stated by the doc itself: no many-plaquette lattice, volume, spacing, continuum.

## Batch 7 — su3/su3_character_certificate.py, certificate_targets.json, su3_results.json (read in full); interval_pivot_witnesses.json (287 KB of pivot endpoints: structure inspected, numbers not eyeballed — to be checked by regeneration, not by reading); frame/LOCAL_FRAME.md, frame_results.json, verify_frame.py (read in full)
- Script: states ordered by shell s=p+q; Schur correction lam^2/(4(d-shift)) applied as diag -2c, adjacent -c on last shell only; interval LDL on 2^-192 grid, banded, fails if a pivot interval meets zero. Targets proposed by SciPy, accepted only by exact inertia: counts (i, i+1) at each enclosure end and exactly 1 for the Schur matrix at z, with hi0 < z < d.
- Note: z is chosen by bisection just below where the Schur matrix's 2nd eigenvalue crosses zero; so certified E1>=z is already tight to the model K_M, and (per my tail_check_01) to the true E1 at 10 and 100.
- d_N: N=3 -> 8; N=6 -> 58/3; N=10 -> 124/3; N=25 -> 195.
- Frame: 65 blocks, K>2mM; residuals ~1e-15 (numerical, 24 trials, not formal). Doc itself: representative Q(A) is not gauge-equivariant; flat measure on Q is not the YM measure.

## Batch 8 — holonomy/HYPERSURFACE_AUDIT.md, holonomy_results.json, verify_holonomy.py; sources/PROVENANCE.json, what_the_hypersurface_keeps.md, SOURCE_AND_PROOF_LEDGER.md (all read in full)
- Audit's 9-row correction table of the "one holonomy theorem" draft: holonomy is not "record+invariance+wall"; walls are not generally discrete; Levine–Tristram jumps only possible at Alexander roots, a root need not jump; APS eta real-valued (circle example eta(0)=1-2a moves with no crossing); S-odd direction can have zero linear response (explicit 4x4 diag family: f'(0)=0, f'''(0)=-5120/81); open-path/Abel integrals are not automatically holonomy; GL2(Z) complement is not a wall; log-capacity census law is for 1D free fermions only.
- Wilson rectangle counterexample in the restart's own graph: Tr W=3-4 sin^2(a/2) sin^2(b/2), F_xy = (i/2) sigma_3 at origin.
- Proposition: A=cU^+dU => Tr(F^F)=0 pointwise (graded cyclicity). Variable weight: Tr(F^F)=2t(t-1) dt ^ Tr(theta^3). BPST frame Q_rho=(rho I, q)/sqrt(D); anti-self-dual; 8 pi^2; nu=-1. 24 SymPy assertions.
- Jeromie's own draft (what_the_hypersurface_keeps.md, 8 Sept): four instances (UPG winding, offset paper Tr K_A with Theorem 10, FOFT Catalan G vs ledger pi^2/6, Kakeya GL2(Z) orbit); slopes 0.5070/1.0140; two independent Z2 labels (eta vs sign L mod 4); census A=2c/pi^2; fences listed in his §5. The audit corrects the unification, keeps the exact determinant/symmetry statements.
- Ledger: source table (SUKS-2, Intrinsic QGT, Spectral Stress 16pp copy, Elemental Peeling r3.0, Matter at a Scale v5, ...); operator-first repo pins; Zenodo catalogue ids; externals (Jaffe–Witten, Massamba–Thompson, Oancea et al., Creutz). Proof status YM-R1..R12 (written proofs + finite checks; 2,723 assertions) and OPEN: YM-O1 gauge-compatible decomposition with useful margins; O2 margins survive volume/continuum; O3 nontrivial continuum theory; O4 frame parameterization vs gauge measure; O5 knot/APS global sector.
- Relevance flag: YM-R5 (normalized Schur coupling c<1), YM-R9 (same observed correlator can hide lower states), YM-R11 (graph action quartic near U=I).

## Batch 9 — sources/RESTART.md (read in full, §§1–11 + refs)
- §2 four projectors kept apart: P_c colour frame, P_s spectral cluster, P_b retained/hidden split, P_Omega vacuum. Spectral split => B=0 => no history kernel.
- §3 Prop 1 graph frame A=theta/2, F=-theta^theta/4; Prop 2 F=Q^+[dP,dP]Q, g=(1/2)Tr(dP dP); bound ||F||_F <= 2 sqrt(g g) (NOT an energy bound). Witness: same scalar QGT g=I/2, curvature norm^2 0 vs 1/2. Warning: restricted-graph action starts at eps^4.
- §4 Prop 3: c=||A^-1/2 B D^-1/2||<1 => lambda_min(H_ex) >= (1-c) min(lmin A, lmin D) (needs vacuum removed first). Prop 4: H_ex >= min(s,d)/(1+kappa)^2. S'(z) <= -I. Sharp failure [[1,1-eps],[1-eps,1]]: block gaps 1, true gap eps.
- §5 Prop 5 principal-angle gluing: H1+H2 >= (a+b-sqrt((a-b)^2+4ab c^2))/2 (I-R); example gap 1-cos(theta). Restriction: YM is not automatically frustration-free.
- §6 history kernel K(t)=B e^{-itD} B^+, self-energy Sigma(z)=B(z-D)^-1 B^+; ||F_off||_F^2 = 2 Tr K(0).
- §7 projector geometry is scale-blind (H -> rH+s); a probe can miss the lowest state (diag(0,eps,1)); Krylov completeness test (16); conditional dense-decay => gap.
- §8 topology labels are not gap scales; Creutz positivity guard on hard admissibility cut-offs.
- §9 target (18) uniform vacuum-excluded bound; transfer form (19): requiring fixed ||T(I-P)||<=q<1 independent of a_t is the WRONG scaling. 0.8^n -> 0 warning.
- §10 2,723 assertions, synthetic; no gauge lattice simulated.

## Batch 10 — sources/HANDOFF_RESPONSE.md (read in full)
- Chat-form version of RESTART.md; same nine results, same limits. Nothing in it beyond RESTART except the summary chain: gauge-compatible representation -> retained matrix curvature and complete probes -> controlled elimination -> uniform vacuum-gap estimate. States the next theorem: uniform estimate for a genuine SU(3) cutoff construction.

## Batch 11 — AI_USE.md, LICENSE, LICENSE-CC-BY-4.0.md, LICENSING.md, CITATION.cff (v1.1.0, 2026-09-27), research/yang_mills_2026_09_09/README.md (read in full)
- Workstream README: starting evidence explicitly includes "the Earth–Moon/Kakeya 8 September evidence review" alongside the paper and Elemental Peeling. Next target stated: spatial-volume and physical-scale control on a genuinely coupled lattice. Policy line: "A failure of a sufficient bound is not a proof of gaplessness."

## Batch 12 — research reports 01, 02, 03 (read in full)
- 01: reruns reproduced 13,587 / 20 / 2,275; restart 2,723; frame 67+411; holonomy 24. Three next investigations: two-plaquette shared link with complete physical subspace; local perturbation theory on full link space (fixed-spacing strong coupling only); energy-resolved hidden bounds and "obstruction caused by discarding extensive spectator ground energy".
- 02: local-window proof (written, not Lean). Budget at alpha=lambda=omega=1, error 1/10: shell cutoff N=12 for 81 links, 13 for 3,000, 15 for 3,000,000 (sufficient bounds, not diagonalizations); one-link Peter–Weyl dims 2,012,920 / 3,436,720 / 9,093,096. Shared-link SU(3) two-plaquette: 7 -> 15 -> 19 gauge states; 19-state full-tail gap lower bounds 4.908928 (lam=1), 4.273698 (2), 2.466778 (3), 0.991383 (4); lam=5,6,8,10,20: NO feasible certificate in the allocation sweep (no gaplessness follows). Independent-plaquette treatment gives error > 4.24 on the rectangle control.
- 03: GaugeCertificates.lean 21 declarations accepted (Lean 4.33.0): exact rational LDL of the 10x10 inner and 7x7 outer matrices => gap >= 4 for shared-link two-plaquette at alpha=lambda=1. Not formalized: Haar integration, basis completeness, positivity improvement, infinite-dim Schur inertia, local-window theorem, volume-uniform stability, continuum.
- FLAG for the pruning question: the two-plaquette certificate DIES between lambda=4 and 5 in that allocation sweep. That is the live search area.

## Batch 13 — reports/04_full_session_report.md (read in full)
- Shared-link two-plaquette model: 7 links, theta graph path lengths 1,3,3; outer rectangle Tr(U V^+) electric energy 8 (independent-plaquette value 32/3 is WRONG). Physical electric subspaces dim 7 (C<=8, floor 28/3), 15 (C<=12, floor 40/3), 19 (C<=40/3, floor 43/3). Non-orthonormal bases keep Gram G: M=S2-S G^-1 S.
- Allocated hidden floor d = s*c_tail + 2*e_local, kappa_local = 7(1-s)/2; inner one-loop certificate checks e_local.
- Table (lower bounds): lam 0.1: 5.281992/5.282106/5.284032/5.284055; 0.5: 4.891209/5.023826/5.100415/5.102788; 1: 2.847077/4.388048/4.883646/4.908928; 2: -/2.417629/3.994564/4.273698; 3: -/0.281765/2.121927/2.466778; 4: -/-/-/0.991383. 25 targets, 94 inertia tasks, 6,570 pivot signs. lam=5,6,8,10,20 inconclusive, not repeated.
- At report time TWO_PLAQUETTES.md, LOCAL_ENERGY_FLOORS.md, SCALING_AND_OBSTRUCTIONS.md, two_sided_targets.json were MISSING from both trees. (They are present in this repo's proofs/ and scripts/ now — to be read next and checked against this statement.)
- Local-window theorem: D_e,N >= E0 + alpha_e c(N+1) - 3 Lambda_e; b_e = 9 Lambda_e/4; error=(omega S+K)/(1-S); gap >= min{omega, mu1-mu0-error}. Transfers a compression gap; does not make one.
- Volume table L=3/10/100 -> N=12/13/15, errors 0.0360331/0.0508983/0.0291327.
- Scaling stress family a=2^-h, alpha=2^h/h, lambda=h 2^h, N=16h: 8,704 controls; NOT a derived RG trajectory.
- Weighted gap-gluing: h_i >= gamma_i Q_i, {Qi,Qj} >= -c_ij(Qi+Qj), delta=min_i(w_i - Sum c_ij w_j)>0 => H >= b delta (I-P_K); counterexample gap 4t/(t^2+1); 5D star weights (10,6,6,6) give >= 1/10, exact 1-sqrt(3)/2. 1,275 assertions. No Lean.
- EARTH–MOON IS ALREADY IN THIS RECORD (§9): 32 million proposals, best 5 triples at 101 edges and best 6 at 102, 44 saved graphs nine-coloured, 77,046 states / 216,587 transitions within 3 flips, 19-vertex necessary edge window 96–102 with min degree 10. Stated there as NOT extra Yang–Mills tests.
- Next obligation stated: positive compression gap uniform in spatial and physical scales with transfer error below it.

## Batch 14 — proofs/TWO_PLAQUETTES.md, LOCAL_ENERGY_FLOORS.md, SCALING_AND_OBSTRUCTIONS.md (read in full; all three are labelled NEW RECONSTRUCTIONS of documents that were missing, not recovered originals)
- TWO_PLAQUETTES: theta graph arms 1,3,3; state energy c(a)+3c(b)+3c(c); exhaustive enumeration through 40/3: 1 (0), 4 fundamental square loops (16/3), 2 rectangles (8), 2 baryonic (28/3), 2 short-arm adjoint (11), 2 short-arm sextet (34/3), 2 adjoint squares (12), 4 sextet squares (40/3) = 19; next floor 43/3 attained. Trace basis with norms (f-g: 4/3; f+g: 8/3; short adjoint 8/9). M=S2-S G^-1 S.
- LOCAL_ENERGY_FLOORS: one cycle h_p on FULL cycle-link space has ground energy = class-function ground energy (positivity improving + uniqueness => gauge invariant). Allocation: beta_e + Sum a_pe <= alpha_e => H >= Sum beta_e C_e + Sum e_p. No commuting, no common vacuum, NOT frustration-free gluing. kappa_p = (1-s) Sum 1/r_e: shared pair 7/2 (1-s); strip ends 7/2, middle 3; corner 3; cube 2. D >= s c_+(R) + E_*.
- SCALING: one-link dim D(N)=(N+1)(N+2)^2(N+3)^2(N+4)(3N^2+15N+20)/2880. Declared family: S, K -> 0 (truncation error only). Obstruction to a METHOD: product of two-level systems h=[[1,-1],[-1,2]], gap sqrt5 for every M, but fixed total-electric cutoff 4 loses the vacuum at M=14 (E0>5) and ground-state mass in any fixed total cutoff -> 0 like poly(M) p^(M-N), p=(1+1/sqrt5)/2. "Fixed total cutoff" is a closed search area by this file itself.

## Batch 15 — proofs/LOCAL_WINDOW_AND_GAP_TRANSFER.md (read in full, §§1–7)
- (2.1) E0 <= E_rest,e + 3 Lambda_e via constant-link Haar trial; (2.2) D_e,N >= E0 + alpha_e c(N+1) - 3 Lambda_e (offset from E0 independent of distant links); (2.3) ||Q V P|| <= b_e=(9/4) Lambda_e using -3/2 <= Re Tr U <= 3.
- §3 one-shell band relation Q_e,N H P_e,N = Q_e,N V_e S_e,N; Sylvester integral; ||Q_e,N R|| <= (b_e/delta_e,N) ||Q_e,N-1 R||, delta = alpha c(N+1) - 3 Lambda - omega; recursion epsilon; factorial-squared envelope.
- §4 product cutoff, S=Sum eps^2, K=Sum b_e eps_{N-1} eps_N (local boundary-tail products, not whole-lattice norm).
- §5 E_j <= mu_j <= E_j + error, error=(omega S+K)/(1-S); gap >= min{omega, mu1-mu0-error}.
- §6 cubic: delta_N = alpha c(N+1) - 12 lambda - omega, b=9 lambda, S=M eps^2; N=O(log M/log log M). What remains: a certified gap of the local-cutoff physical Hamiltonian uniform in volume. Initial cutoff diverges toward weak electric coupling.
- §7 prior: Tong et al. 2022; Yang–Kane–Jabeen 2026; Ciavarella et al. 2025/26.

## Batch 16 — scripts/two_plaquette_certificate.py, two_plaquette_targets.json, two_sided_targets.json (read in full)
- 7-state basis 1, TrU, TrU^+, TrV, TrV^+, Tr(UV^+), Tr(VU^+); electric (0, 16/3 x4, 8 x2); tail 28/3. Exact Haar by Weingarten (degree <= 4 per variable, refuses beyond). M = S2 - S^2 (orthonormal here), PSD checked by all principal minors. Certificate: inertia 1 at r, 1 at z, 1 for Schur at z.
- 7-state bare targets: lam 1/10: gap 5.281992; 1/2: 4.891209; 1: 2.847077; 6/5, 7/5, 3/2 smaller.
- two_sided_targets.json IS present here (report 04 said missing): ground lower / first upper pairs. Row 3 (reads as lam=1): E0 >= 5.794672, E1 <= 10.725856 => gap <= 4.931184 against certified lower 4.908928. If the row/lambda mapping holds, the lam=1 two-plaquette certificate is within 0.023 of the truth. (Mapping to be confirmed when the program that consumes this file is read.)

## Batch 17 — scripts/two_plaquette_extended.py (read in full as a complete diff against the 7-state script), two_plaquette_extended_targets.json
- 15-state basis adds baryon f-g, short adjoint TrU TrV^+ - Tr(UV^+)/3, short sextet f+g (+ conjugates), |TrU|^2-1, |TrV|^2-1; Gram diag (1 x7, 4/3 x2, 8/9 x2, 8/3 x2, 1 x2); tail 40/3. Haar extended to degree 6 ((3,3) Weingarten 7/120, -1/40, 1/60; (4,1) and (6,0) via invariant bases).
- certify_row: inner one-loop floor e proven by the single-loop interval Schur matrix at coupling lam/kappa being positive definite (0 negative pivots), kappa = 7/2 (1-s); outer floor d = s*TAIL + 2e.
- Targets (15-state): s = 19/20, 19/20, 9/10, 4/5, 7/10 for lam = 1/10, 1/2, 1, 2, 3; inner N=25 each. The retained fraction s has to DROP as lambda rises — the allocation gives more electric weight to the local floors.

## Batch 18 — scripts/two_plaquette_19.py (full diff vs extended), two_plaquette_19_targets.json; scripts/su3_character_certificate.py (byte-identical to the paper copy); scripts/certificate_targets.json (same content, compact formatting)
- 19-state adds chi6(U), chibar6(U), chi6(V), chibar6(V) at 40/3; tail 43/3.
- 19-state targets: lam 1/10 s=19/20; 1/2 s=19/20; 1 s=9/10; 2 s=33/40; 3 s=29/40; 4 s=5/8 with r=20.408295, z=21.399678, d=23.482681.
- OBSERVATION (to test, not yet tested): two_sided_targets row 6 has ground_lower 18.804066 and first_upper 25.823373. If row 6 is lam=4, the true E1 (<= 25.82) may sit ABOVE the hidden floor d=23.48, and a Schur certificate can never certify z >= d. Then the lam >= 5 failures are a cutoff-size wall (true E1 passes the tail floor), not a sign of a closing gap.

## Batch 19 — scripts/lifted_two_plaquette_certificate.py, two_plaquette_lifted_targets.json, local_window_budget.py (read in full)
- Lifted (7-state allocated) targets, 8 rows lam = 1/10, 1/2, 1, 6/5, 7/5, 3/2, 2, 3 with s = 19/20, 37/40, 17/20, 33/40, 4/5, 31/40, 29/40, 23/40; inner N=20. The lam=1 row (s=17/20, kappa=21/40, e=2.130877, d=12.195087, r=5.801018, z=10.189066) is the one whose simple margin >=4 went to Lean (r=6, z=10, d=182/15, e=21/10).
- Six destruction controls must be refused (s=1, wrong kappa, free d, floor too high, r=z, N=0).
- Budget script: epsilons recursion exactly as in the proof; cubic uses incident = 4 lambda; link_dimension(1)=19; default sweep lam in {0, 1/10, 1, 10, 100} x L in {3, 10, 100}.

## Batch 20 — research lean/ (README, lakefile, toolchain, FalseControl; GaugeCertificates.lean byte-identical to the root module already read), recovered_uncommitted/README.md, run_all.py (read in full)
- Lean scope restated: inner 10x10 certifies e=21/10 at kappa=21/40; outer 7x7 with s=17/20, d=182/15, r=6, z=10 => gap >= 4.
- run_all.py accounting check: (gaps, inertia, pivots) must equal (25, 94, 6570); it needs two_sided_spectral_checks.py + two_sided_targets.json (README says the json was not recovered; a two_sided_targets.json does sit in scripts/ in this repo — provenance of that file unexplained by the README).

## Batch 21 — recovered_uncommitted/scripts: two_sided_spectral_checks.py, scaling_controls.py, spatial_stability_checks.py (read in full)
- two_sided: rows pair one-to-one with two_plaquette_19_targets (lam 1/10, 1/2, 1, 2, 3, 4) — mapping CONFIRMED. ground_lower: K_M(l) positive definite (0 negatives) => E0 >= l; first_upper: 19-state compression has >= 2 eigenvalues below w => E1 <= w (Rayleigh–Ritz).
  Enclosures of the true two-plaquette gap: lam=0.1 [5.284055, 5.284076]; 0.5 [5.102788, 5.103880]; 1 [4.908928, 4.931184]; 2 [4.273698, 4.811089]; 3 [2.466778, 5.226349]; 4 [0.991383, 7.019307].
  So the certificate is tight to 4 digits at 0.1, to 0.5% at 1, and wide open at 3 and 4. At lam=4 the Ritz E1 (25.82) is above the hidden floor d (23.48): the lower certificate cannot follow E1 there. Whether the TRUE E1 is above d is untested (Ritz value is only an upper bound).
- scaling_controls: checks envelopes for h=2..30; rows R in {1,2,10}, h in {2,3,4,6,8,12,16,20}.
- spatial_stability: periodic cubic incidence for L=3..7 (each link in 4 plaquettes; 4-site patches cover each site 4 times); normalized perturbation coefficient 81/4; rejects the "unique local ground" claim for a one-site patch extended by spectators (8 zero-energy states).

## Batch 22 — recovered_uncommitted/tests: test_local_window.py, test_su3_independent.py (read in full)
- test_local_window: U(1) rotor chain (length 2,3; k=4; lam 0, .1, .5, 2; omega .3, 1.5, 4; N 0..3) tests each inequality of the local-window proof against the actual matrices; 100 dense complex cases where the zero-leakage claim must fail. Rotor analogue only.
- test_su3_independent: electric operator applied as 3 C_U + 3 C_V + C_diag (diag = shared link acting on both) via Gell-Mann second derivatives; the independent-plaquette form 4C_U+4C_V must be wrong by > 1 on the rectangle states; 100,000 Haar pairs vs exact Gram/S/S2 within 8 SE.

## Batch 23 — cross_theorem/README.md, REPORT.md (read in full)
- "Requested ... after the Earth–Moon side-scanner integration" — the cross-theorem round was built right after the Earth–Moon work, using Light Keeps the Ledger (energy-resolved boundary record), Elemental Peeling (exact elimination/memory), Kakeya dual-obstruction.
- Five open-boundary original-link graphs, complete C<=8 physical space = constant + both orientations of every 4- and 6-cycle (triangle-free, K2,3-free grids), tail >= 28/3: two squares (7 links, dim 7), three-square strip (10, dim 11), three-face corner (9, dim 15), full cube (12 links, 6 faces, cycle rank 5, dim 45), two adjacent cubes (20 links, 11 faces, 9 cycles; 60,459 supports checked; 11 four-cycles + 36 six-cycles => dim 95).
- K_floor <= K_res <= S <= A-z with K_res = A - z - lam^2 Sum_e M_e/(s e + E_* - z). Table (one floor / resolved): 4.388047/4.696420; 3.912389/4.366060; 3.817251/4.280636; cube 1.649349/2.109917 (lam=1); two cubes 3.295750/3.817691 (lam=1/2). At lam=1 two cubes: allocation grid INCONCLUSIVE.
- Frozen-parameter control: old comparison matrices have 3, 4, 4, 31, 23 negative directions, resolved have exactly 1.
- Safe binning inequality (two moments M0, M1 per bin); mean-energy substitution is UNSAFE (1/10+1/14 > 2/12). Cube 3 bins => gap >= 2; two cubes 2 bins => gap >= 7/2 at lam=1/2.
- Kakeya instance: ker M = span(e0); y0 M + y1 M A = e0^T; 173 scalar equalities over the five graphs; rank(M)=n-1, rank(M+AMA)=n.
- Vertex-only sharing gives exactly zero kinetic cross term.
- Yarotsky Theorem 1 applied: fixed spacing, sufficiently small lam/alpha => volume-independent gap; perturbation bound 81(lam/alpha)/4; NO numerical threshold; does not reach lam/alpha=1.
- Interval extension: cube lam in [0.95,1.05] gap >= 0.759917; two cubes [0.45,0.55] >= 1.342691.
- Prior: Balaji et al. PRD 113, 094505 (2026) already studies an SU(3) cube; Li et al. 2608.27267 maximal-tree gauge.
- Next task stated: useful comparison under growth in spatial volume with consistent normalization, without losing the interacting vacuum.

## Batch 24 — cross_theorem/proofs: RESOLVED_BOUNDARY.md, PARAMETER_AND_POLE_BOUNDS.md, BOUNDARY_OBSERVABILITY.md (read in full)
- RESOLVED_BOUNDARY: THIS IS THE WRITTEN PROOF OF THE LEAN HYPOTHESIS `hResolvedLeSchur` (K_res <= S). Chain: allocation gives the OPERATOR inequality D >= T = s C_Q + E_* (D and C_Q need not commute); inverse order (variational formula <x,A^-1 x> = sup_y[2Re<x,y> - <y,Ay>]) gives B(D-z)^-1 B* <= B(T-z)^-1 B* = lam^2 Sum_e M_e/(s e + E_* - z), M_e = P S Q E_e Q S P. Finite Casimir support of Ran(QSP): per link {4/3}, {4/3,10/3}, {0,3}; Lagrange projector L_e(C). So in Lean the statement is assumed only because unbounded-operator inverse monotonicity + Haar + Peter–Weyl are not formalized; on paper it is closed.
- Prohibited shortcuts recorded there: D >= T does NOT give exp(-tD) <= exp(-tT); a floor on boundary-COUPLED states only is not a floor on the hidden space (A=diag(0,2), D=diag(1/10,10) example: dark hidden mode at 1/10); rank alone does not give a gap (M1 vs M2 example, 2 vs 1 negative directions).
- PARAMETER: gap(lam+delta) >= gap(lam) - (9/2) P |delta|; cube 2.109917 - 27/20 = 0.759917 on [0.95, 1.05]. Pole degree: determinant degree <= rank M_e in each t_e; summed ranks 16/46/59/259/9 vs 49/110/150/495/15.
- OBSERVABILITY: O_k = Sum A^j M A^j, ker O_k = intersection ker(B^+ A^j); in all five models ker M = vacuum line and O_1 = M + AMA > 0 (cube: rank 44 -> 45). Proves completeness of the retained observation only.

## Batch 25 — cross_theorem/proofs: EXACT_KAKEYA_GAUGE_INSTANCE.md, POSITIVE_ENERGY_COARSENING.md, FIXED_COUPLING_STABILITY_MAP.md, SPATIAL_BASES.md (read in full)
- KAKEYA: CanForce(T,b) := exists x, Tx=0 and bx != 0; dual_certificate: b = y∘T excludes CanForce. Instance: y1 = e_j^T/(MA)_{j,0}, then solve y0 M = b - y1 MA. 173 equalities (7+11+15+45+95; earlier prose said 171, corrected).
- COARSENING: chord inequality; resolved <= binned <= global-floor penalty; averaging before inversion is the wrong direction (1/210 excess).
- YAROTSKY map: on-site space = three links at a site; h_x = (3/4) Sum_{y in x+Lambda0} k_y (gap >= 1 on the 4-site patch); phi_x centered, ||phi_x|| <= (81/4) rho; Sum(h_x+phi_x) = (3/alpha)H - const. For rho small enough: gap(H_L) >= alpha gamma/3 for all L. beta_*, gamma NOT computed. So: volume-uniform gap at fixed spacing and small lambda/alpha is CLOSED (established theory); the open part is a NUMBER for the threshold and anything at moderate/weak coupling.
- SPATIAL_BASES: support theorem (min degree >= 2; C<=8 allows <= 6 occupied links); pure-electric gap on a graph of girth g is exactly 4g/3. Graph lemma: simple, triangle-free, K_{2,3}-free => every support with <= 6 edges and min degree >= 2 is ONE simple cycle of length 4, 5 or 6. Hence complete C<=8 space = constant + oriented fundamental loops of all such cycles, tail >= 28/3, for the whole graph class. Table: two-square (6 v, 7 links, 2 four-cycles, 1 six-cycle, dim 7); three-square strip (8, 10, 3, 2, 11); corner (7, 9, 3, 4, 15); cube (8, 12, 6, 16, 45). Periodic length 1, 2, 3 cells break the simple-graph/girth-4 argument (self-loops, parallel links, noncontractible 3-cycles).
- Kinetic term must be applied on ORIGINAL links before tree contraction (Fierz identity); vertex-sharing gives no cross derivative.
- This graph lemma is the one place in the repo where a pure graph-combinatorics argument (the Earth–Moon kind) carries a Yang–Mills step.

## Batch 26 — cross_theorem/lean (README, lakefile, FalseControl; CrossTheorem.lean byte-identical to root), sources/KakeyaForcingLinear.lean, scripts/gauge_polynomials.py (read in full)
- Kakeya source: CanForce, forcing_iff_kernel_not_le, dual_certificate, presentation_invariant, nonzero_target_rescaling, shifted_operator_on_kernel, inverse_on_kernel, projector_detects_forcing (P fixes ker A, A∘P=0, symmetric => forcing iff <v,Pv> > 0), three rational label lemmas.
- gauge_polynomials: trace words reduced and cyclically normalized; electric action via Fierz on original links (4/3 per occurrence; pairs on a shared link: -c/3 plus join/split term); Haar per edge via Weingarten; tree_reduce only for integration; casimir_candidates gives the overcomplete energy support; spectral_parts applies the Lagrange projector by repeated (C - t)/(e - t).

## Batch 27 — cross_theorem/scripts/spatial_gauge.py (read in full)
- Six declared graphs: two, strip, corner (cube graph minus vertex 111), cube, double_cube (3x2x2 grid points), vertex_wedge (control). Basis = constant + both orientations of every cycle of length <= 6; Gram must be exactly the identity; S, S2, M = S2 - S^2 from exact Haar on tree-reduced words; energy-resolved masses M_e must sum exactly to M; low-energy closure check (components at e <= 8 must lie in the retained basis); support_check enumerates all edge subsets of size <= 6 and requires every min-degree>=2 survivor to be a single 4- or 6-cycle.

## Batch 28 — cross_theorem/scripts/spatial_certificates.py, native/targets.py (read in full)
- validate_target: allocation coefficient per face = Sum over its links of 1/(number of faces on that link); local floor per face certified by the single-loop interval Schur matrix at coupling lam/kappa; floor d = s*28/3 + Sum e_p must equal the stated d; inertia (1,1,1) at r, z and for K (scalar_floor or resolved) on the 2^-192 grid; every M_e PSD.
- propose: s searched on the grid k/20 only; inner N=12.
- 58 targets. Highest coupling with an accepted target per graph: two squares 2; strip 2; corner 2; cube 1; double cube 1/2. Read off the rows: cube lam=1 has r=17.440958, z=19.550875, d=19.968817; double cube lam=1/2 has r=16.242155, z=20.059846, d=20.603685.
- PATTERN (from the stored rows, not a new test): the largest certifiable coupling FALLS as the graph grows (2, 2, 2, 1, 1/2). The usable window is d - r = s*28/3 - (E0_upper - Sum e_p): a fixed electric allowance minus an allocation deficit that grows with the number of plaquettes. This is the same wall SCALING_AND_OBSTRUCTIONS.md proves for a product model.

## Batch 29 — cross_theorem/native/machine.py (read in full)
- Compound Eye instrument 1.0.1: hash-chained registry of eye versions and sets (no version may be replaced), dependency DAG, context contract (object/model/basis/boundary/coordinate/unit/source), statuses ok / blocked / inapplicable / error, exclusive-create run files. Infrastructure; carries no mathematics of its own. Scope line: "Shared evidence is not counted as independent confirmation."

## Batch 30 — cross_theorem/native/ym_eyes.py (read in full)
- 14 observers + 3 set outputs + 1 whole: identity, support (also re-checks triangle-free and K2,3-free), gram (M = PS^2P - (PSP)^2, PSD), energy_labels (masses sum to M, ranks), allocation (local floors), certificate (inertia 1,1,1), comparison (scalar_floor vs resolved at identical parameters; difference PSD), observability (rank n-1 -> n after one retained step, at lam=1), dark_guard (dark hidden level counterexample), window_guard (refuses borrowing a gap from another graph/cutoff; lists the three missing items), source_transfer (what was and was NOT carried from Light / Elemental / Kakeya / Offset), parameter_guard (interval half-width 1/20, Lipschitz (9/2)P).
- whole(): next_required = "Control a gap for growing spatial systems in a consistent physical normalization; do not reuse a different model's gap." independent_votes=0.

## Batch 31 — cross_theorem/native/recheck.py, ym_forcing_eye.py, ym_energy_bins.py (read in full). END of research/yang_mills_2026_09_09/ (all 57 files read).
- recheck: rebuilds five matrix records from original links, checks pinned digests, registers 18 eyes, expects 18 ok per model, 4 false-premise controls (false hash, alpha=2, d=100, gap borrowed from the cube) must not return ok.
- forcing eye: constructs y0, y1 with y0 M + y1 M A = e0^T exactly; corrupted row must be detected.
- energy bins: cube lam=1 margin 2 with 3 bins; double cube lam=1/2 margin 7/2 with 2 bins; checks exact < binned < scalar_floor penalty ordering by PSD elimination.

## Batch 32 — the four other branches (complete two-dot diffs against main read)
- tidy-2026-10-26: older state; main = tidy + SchurInertiaCount.lean (+ doc lines). Nothing on it that main lacks.
- formal/schur-inertia-count-2026-09-27: Lean identical to main; 36 changed lines are the byline only ("Jeromie N. Beasley" there vs "Jeromie Beasley" on main).
- research/yang-mills-complete-record-2026-09-27: 79-theorem state, no SchurInertiaCount; nothing main lacks.
- add/positive-response-feedback-2026-09-28: HOLDS THREE THEOREMS THAT NEVER REACHED MAIN, in CouplingFeedback.lean: `feedbackWith_diag`, `feedbackWith_eq_zero_iff_of_posDef` (positive-definite hidden response R: B R B^T = 0 iff B = 0), `nonzero_coupling_gives_nonzero_posDef_feedback`. Its inventory says 82 (79 + 3) and it lacks SchurInertiaCount; main has 80. Union would be 83. Provenance: adapted from operator-first research/upg/formal/UPGPositiveFeedback.lean at c4e045d41642.

## Not read by eye
- paper/2026-09-08/su3/interval_pivot_witnesses.json (287 KB of integer pivot endpoints) — checked by regeneration instead (see window_wall_01 output).
- The paper PDF (same text as the .md per report 01; not opened).

## COVERAGE: yang-mills-lean main at 0b627d8 — every text, Lean, Python, JSON-target and workflow file read in full, plus the full differences of all four side branches.
