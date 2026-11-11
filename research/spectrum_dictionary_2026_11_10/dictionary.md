# Yang–Mills track: physical quantities vs our constructions
Kept by Spectrum for Red's YM plan (started 2026-11-10). Fill in sources as the round-five record lands.

## Physical (standard lattice / QFT meaning)
| Symbol | Meaning | Status |
|---|---|---|
| H_G | Lattice Yang–Mills Hamiltonian for gauge group G | standard |
| gap(H_G) | Spectral gap: first excited minus ground energy | standard; target of the inequality |
| g | Gauge coupling; in the usual lattice form coefficients are g²/2 (electric) and 1/g² (magnetic) | standard (Grey) |
| ground energy E_0(κ) | Lowest eigenvalue as a function of a coupling parameter | concave only if H is linear in that parameter |

## Our constructions (Jeremy's framework / plan, not standard physics)
| Symbol | Meaning in the plan | Status |
|---|---|---|
| ω | Floor term in gap ≥ min{ω, …} | needs source in round-five record |
| μ̲₁, μ̄₀ | Certified lower bound on level 1, upper bound on level 0 | ours; from certified endpoints |
| S_G, K_G | Compression/leak terms in (ωS_G + K_G)/(1−S_G); need S_G < 1 | ours; definitions pending record |
| d − r | Quantity the window wall bounds | sign pending (Grey) |
| W(s) | Window function, W(0)=0, assumed concave | ours; concavity is a hypothesis |
| κ, λ | Parameters entering H | must enter linearly (Grey to check) |

## Lean already on the shared computer (not pushed)
- Lean Green: /workspace/window_wall_lean/WindowWall.lean (5 thms; certified-point wall W(h) ≤ 0 ⇒ W(s) ≤ 0 for s ≥ h; derivative-free secant; false control s²−s)
- Green: /workspace/colour-team/green/ym_window/WindowWall.lean (6 thms; derivative wall needs W′(0) ≤ 0, i.e. an UPPER slope bound)
- Note: the certified-point version avoids needing an upper bound on W′(0).

## Open
- Round-five record (scripts + results) not yet received.

## Update 2026-11-10 8:03 PM CT (from Grey, yang-mills-lean main, paper/2026-09-08/YANG_MILLS_CONTINUATION.md and SCALING_AND_OBSTRUCTIONS.md)
- One-plaquette H = κC₂ + λ(3 − Re χ₁,₀); many-link H = Σ αₑCₑ + Σ λₚ(3 − Re Tr Uₚ). κ, λ enter linearly ⇒ E₀(κ,λ) concave jointly. [physical operator, repo definition]
- d = omitted-sector floor; shell d_N = (κ/3)(…), linear in κ, no λ. [ours]
- r = variational ground endpoint. Fixed trial vector ⇒ d − r linear; true E₀ ⇒ d − r convex (not concave). Concavity wall applies to E₀, not d − r. [ours]
- Sign: d − r > 0 good (certificate works); d − r ≤ 0 window closed; crude-floor d − r ≤ 0 does NOT imply gapless. [repo]
- Scaling family α = 2ʰ/h, λ = h·2ʰ: nonlinear in h/g; wall only along κ or λ with others fixed.
- Open for Jeremy: does the wall bound E₀ or d − r?
- Window-wall Lean now in yang-mills-lean PR #5 (Lean Green's derivative-free version primary).

## Update 8:05 PM CT: round-five record located (from Jeremy's outside session)
- Location: dicipler-pixel/votkp-lean, branch claude/votkp-research-20261110, research/2026-11-10/round5/ (commit bdb51cd); window_wall_01.py + .out/.json. Not in yang-mills-lean yet.
- W(s) = s·(28/3) − Σ_p [g(c_p) − g((1−s)c_p)]  [ours; uses LOCAL_ENERGY_FLOORS.md eq 1–2]
- d = s·(28/3) + Σ e_p, e_p ≤ g((1−s)c_p, λ) [certified local floors]; r ≥ E0 ≥ Σ g(c_p, λ).
- g(κ,λ) = ground energy of κC₂ + λ(3 − Re χ) [physical operator]; concave in κ; g′ = ⟨C₂⟩ ≥ 0.
- W concave in s because each g((1−s)c_p) is concave in s, so this resolves Grey's d − r convexity worry: the wall bounds d − r via W, which is built from g.
- W′(0) = 28/3 − Σ c_p g′(c_p): a LOWER bound on g′ gives an UPPER bound on W′(0). Forward secant is the right one.
- g_low: one-loop Schur verifier; g_up: Rayleigh–Ritz with exact inertia.
- Status: 58 targets obey d − r ≤ W(s), min slack 0.000276; slopes are floats (cutoff 45), not certified. Marginal: strip −0.13, corner −0.42 at λ = 5. Outer bound only.

## Update 8:05 PM CT (Grey check of window_wall_01.out, bdb51cd)
- Max violation of d − r ≤ W(s) over 58 targets: −0.000276 (all have room).
- W′(0) < 0 (excluded): two-plaquette λ=10; strip λ=5,10 (−0.127, −10.57); corner λ=5,10 (−0.424, −10.32); cube λ≥3; double cube λ≥2. None overlaps the 58 stored targets.
- Slopes from g′ = ⟨C₂⟩ in float ground state (cutoff 45), not secants. Only strip/corner at λ=5 could flip once certified.
- Lean restatement: Red will use right derivative of concave g (exists at level crossings); W′(0+) uses left derivative ≥ right ≥ forward secant.

## Update 8:08 PM CT: certified slopes (two independent runs, not pushed)
- Green (/workspace/colour-team/green/ym_window/endpoints/, h = c/1000, cutoffs 20 & 28): strip λ=5 W′(0) ≤ −0.121; corner λ=5 ≤ −0.417; all other negative-slope cases certify excluded; λ=4 strip/corner controls not excluded.
- Lean Green (/workspace/lg_ww/, exact rational, h = 1/100, N = 14 & 18): strip λ=5 ≤ −0.108; corner λ=5 ≤ −0.404; false lower bound (+0.001) rejected.
- Both agree: marginal cases excluded for this allocation class. Outer bound only.
- ink: r ≥ Σ g(c_p) holds (honest operator split, electric shares 1/r_e sum to α_e). c_p values match LOCAL_ENERGY_FLOORS.md; 28/3 = model tail floor, same as in d.
- Limits: α = 1 hard-coded (scaling family needs rescaling); only the even allocation a_pe = (1−s)/r_e is covered.

## Update 8:10 PM CT
- Main lemma (GPT form, ink reviewed): L_p = (g_low(c_p+h_p) − g_up(c_p))/h_p; W(s) ≤ s(28/3 − Σ c_p L_p) for s ∈ (0,1]; no strict window if Σ c_p L_p ≥ 28/3. Derivative-free; concavity holds down to κ = 0 (g(0)=0).
- 28/3 = C₂(4,0), first Casimir above cutoff 8; omitted-sector floor c₊(R), eq. (2); hard-coded tail=F(28,3). [repo constant, not fitted]
- e_p: certified lower bound for κ_p = (1−s)Σ1/r_e; c_p = Σ1/r_e. r ≥ Σ g(c_p) is eq. (1) with β = 0 (s = 0 limiting case; state in Lean).
- Controls: double cube λ=1/2 not excluded (≤ +8.64); λ=1 ≤ +6.22; cube λ=2 ≤ +3.25. Double cube λ=2 excluded (Σ c_p L_p ≥ 11.92, W′(0) ≤ −2.586).
- Lean Green reran Green's script at N=24: same. Grey reran window_wall_01.py: identical.
- Records in PR #5: round5/ (db1dd9c), window_wall_endpoints/ (4fd94c0, c9c44fd).

## Update 8:35 PM CT: Coxeter bridge (coxeter-rank2-lean main 3c789a1)
- SU(3) Casimir c(p,q) = (p²+pq+q²+3p+3q)/3, from inverse Cartan of A2 (1/3)[[2,1],[1,2]] [standard physics; Spectrum checked]
- tits_positive_definite at (1,1) = positivity of that form (single-link Casimir growth). It does NOT by itself give the 28/3 total-Casimir tail floor; that needs the graph/gauge-invariance combinatorics (ink).
- Proposed: gate.py statement-parity lock + banned-token check for yang-mills-lean.

## Update 8:53 PM CT
- Claude's 10 frozen statements: first-excluded cells two squares λ=8, strip 5, corner 5, cube 3, double cube 2.
- Two squares (Grey float, cutoff 45): W′(0) = +1.48 (λ=6), −0.04 (7), −1.45 (8), −2.77 (9). λ=8 plausible; not yet certified by our crew (certified only at λ=10, ≤ −4.01).
- 28/3 floor proof: SPATIAL_BASES.md (all five graphs); 40/3, 43/3 only for two-plaquette, TWO_PLAQUETTES.md. Lean route (ink): layer 1 single-rep bounds + layer 3 graph combinatorics proved; layer 2 (SU(3) Peter–Weyl/tensor rules) as hypotheses. Open-boundary, α = 1 only.
- DihedralBridge m=1 = Mathlib CoxeterMatrix.I m (m+2 off-diagonal) → I₂(3), order 6, SU(3) Weyl group.
- PR #5 merged; #6 write-up + certify_58_windows; #7 WindowWallMono. scripts/config.json lists 14 modules/80 theorems; window-wall files not yet kernel-replayed/axiom-audited (Claude folding in).
- 8:54 PM CT: PR #7 merged; main 119b8b0 (WindowWall, WindowWallDeriv, WindowWallFinite, WindowWallMono). Red certified two squares λ=8 (W′(0) ≤ −1.448) and λ=7 (≤ −0.037), N=24; with monotonicity, two squares excluded for all λ ≥ 7.
- 8:59 PM CT: PR #8 (Green, OneLinkTailFloor: p+q ≥ n+1 ⇒ C₂ ≥ tail_floor(n), exact) on verify-gate; PR #9 (Lean Green, gate: banned tokens + 20→23 frozen statements). #8 needs rebase onto 071335b after #9.
- GPT recheck: five cells clear 28/3 by 1.451 (two squares λ=8), 0.124 (strip 5), 0.420 (corner 5), 2.031 (cube 3), 2.589 (double cube 2). Open: config.json audit must include WindowWallMono (→19 modules/111 theorems, before #8); PR #6 scripts need paths relative to their own location.
- Two squares first certified exclusion is λ=7 (≤ −0.0367); λ=8 used for provers.

## Round 6 additions (2026-11-10, 9:28 PM CST)
- ink: TailFloor.lean (local, Lean 4.36.0-rc2, no sorry/native_decide, standard axioms). Layer 1 proved (3·C2 ≥ 4 nontrivial; ≥ 9 for p+q ≥ 2; C2(3,1)=25/3 pinned). Layer 3 by decide +kernel on two/strip/corner/cube (cube: 22 supports = 6 squares + 16 hexagons; K2,3 control fails correctly). Layer 2 (SU(3) rules) = hypothesis `SupportHyp`. Double cube not covered (OOM). Red: open as own PR after #9.
- GPT (OURS, certificate-family statements, not physical spectrum):
  - Uneven splits with common s: Jensen on concave nondecreasing g gives Σ g(κ_p) ≤ P g((1−s)c), c = E/P; equal face coefficients realizable (exact integer flow). d − r ≤ −sδ. δ ≥ 1.452038 (two squares λ=8, c=7/2), 0.138547 (strip λ=5, c=10/3), 0.421398 (corner λ=5, c=3), 2.031478 (cube λ=3, c=2), 2.601404 (double cube λ=2, c=20/11). Even per-link split is suboptimal on strip and double cube. Still open: s varying per link.
  - Independent graph count: all supports ≤ 6 links on all five graphs; double cube 60,459 subsets, 47 survivors, all single squares/hexagons. Graph step of 28/3 confirmed independently of ink. SU(3) step still open.
  - Two-plaquette floors 40/3 and 43/3 argued sharp (theta graph arms 1,3,3; 8⊗3 ∋ 3).
  - Double cube: trial-state bound U(λ) = 28/3 + (20541500575676903/909090909514080)λ (α=1); interval check excludes every λ/α ≥ 0.9867. Last feasible coupling in (0.5, 0.9867) unresolved.
  - Scaling: common α>0 → exclusions hold at μ = λ/α.
  - Gate (#9): rejects sorry, declared axiom, changed frozen hypothesis; BUT a change to unfrozen WindowWallDeriv.slope_far_le_near passed --gate-only → new cell statements must be added to the frozen list. PR #10 CI green: 18 modules / 107 theorems; with WindowWallMono 19 / 111, config still omits it.
- Green: PR #8 merged 071335b in (no force-push), gate 23 frozen matching, mergeable; ready after #9.
- Green independent support count (support_count.py/.json in green/ym_window/support_count/): double cube 60,459 subsets → 47 survivors (11 squares, 36 hexagons); other graphs match GPT. Graph step of 28/3 now double-checked on all five graphs.
- Red's open list: SupportHyp (SU(3) step) → ask GPT for Lean-ready proof; double-cube boundary in (0.5, 0.9867); add new cell statements to frozen gate list; PR #10 config add WindowWallMono (19/111). Merge order #9 then #8; #6 when Jeremy says.
- Grey rechecked uneven split (common s) with Green's N=24 bounds, h=c/1000: δ = 1.4482 / 0.1343 / 0.4175 / 2.0278 / 2.5971 (all positive, slightly below GPT's). Slope = E·L(c) − 28/3. Closed for common s; open: per-link s, SupportHyp. 0.9867 matrix bound not yet rechecked by team.
- Lean Green PR #9 commit 0287623: gate now freezes every theorem in the four window-wall files ("complete_files"); 21 frozen; tests: weakened slope_far_le_near fails, unfrozen dummy fails, clean passes. #8 will need JSON merge again (keep both; optionally add OneLinkTailFloor.lean to complete_files).
- ink: double cube count matches (47 = 11 squares + 36 hexagons). New streaming checker with `checkB_sound : checkB g = true → SupportHyp g` (standard axioms); `#eval checkB dcubeE = true`, but `decide +kernel` OOM locally (~2 GB free) → separate check in PR; if it fails, PR says double cube not covered. Jeremy said "go" (9:36 PM CST) → ink opens own PR after #9.
- NAMING NOTE: earlier `SupportHyp` was described as the SU(3) layer-2 hypothesis; here it names the graph-side conclusion. Confirm in PR which name is the SU(3) assumption vs the graph property, so the open SU(3) step isn't read as proved.
- PR #11 (ink, 18a5a3b on main 119b8b0, Lean v4.33.0): 28/3 tail floor layers 1+3 for two squares/strip/corner/cube; SU(3) layer 2 = hypothesis `SupportHyp`; α=1, open boundaries; double cube NOT covered (TailFloorDoubleCube.lean outside build; Lean Green to try decide +kernel with ~11 GB). TODO: add TailFloor to config.json + frozen list; lakefile merge with #8. Naming split (SU(3) assumption vs graph property) still to confirm.
- PR #8 now has 0287623 + 1b061a5 (OneLinkTailFloor in complete_files); gate 25 frozen matching.
- PR #11 naming fixed (818a7d2): graph property = `SmallSupportsAreCycles` (proved); SU(3) step = "gauge support rule", marked NOT proved, NOT formalized. Double-cube check: branch ink-tail-floor, `lake env lean TailFloorDoubleCube.lean`, theorem `dcube_cycles` (Lean Green running). Merge order: #9 → #8 → #11 (CI green each); Lean Green alone edits config.json, complete_files, lakefile.
- Lean Green: dcube_checkB decide +kernel OOM at ~11.4 GB / 2.5 min on v4.33.0 → stays outside build; needs per-cycle split or cheap reflection proof. #9 CI green.
- Jeremy shared (10:32 PM CST, outside sessions, not ours): AK 5/3 cell closed (385,888,720 configs, exact mod 2^31−1 rank via Hadamard bound; false seeding/symmetry lemma withdrawn), and an open-math review of the Coxeter rank-2 repo (commit 12dec83): post-freeze syntax edit should be recorded; radical dim = 1 at ab=4 dropped, restorable via m6 count; swarm ran Lean 4.33.1 vs pinned 4.33.0.
- Transfer lessons for YM: no symmetry WLOG in the double-cube split unless proved for that graph; record any post-freeze statement edit; build on the pinned Lean version.
- Red's no-enumeration graph argument (min degree ≥2, triangle-free/bipartite, ≤6 links → single cycle; theta only 2,2,2 needs 3 common neighbours; cube/double cube max 2) checked by Spectrum and Green; add figure-eight / path-joined two-cycle case (≥8 links). Red adopted team rules: record post-freeze syntax edits; never drop hard conjuncts (named theorem or open list); only CI on pinned v4.33.0 counts.
- Coxeter: radical theorems already in (30dfb2a, 53909ac); freeze log + pinned swarm builds in 5712d3e.
- Kakeya (outside): Grey flags 16,807 = 7^5 not 7^7 → ask GPT whether two edges pinned or pool smaller before claiming "all seven edges labelled".
- #8 and #9 CI green.
- 10:42 PM CST: Red merged #9 then #8; main 5c870cf (gate + OneLinkTailFloor in). Lean Green owns TailFloor config/complete_files/lakefile on #11. ink owns double cube (Red's short proof; ink currently trying per-branch kernel split); Green is fallback, no symmetry shortcut.
- Kakeya ZIP (AK_5-3_cell_unpruned_v1.zip) to Lean Green; search outputs only verdicts, no Lean-checkable certificates → needs per-case certificate output (as combined paper Thm 23) or verified search. Grey's 7^5 vs 7^7 labelling question still unanswered.
- PR #11 b5f5824 (Lean Green): lakefile lists OneLinkTailFloor + TailFloor; config.json adds TailFloor (expected 80 → 97 theorems); complete_files incl. TailFloor.lean; gate 42 frozen. Main config lacks window-wall modules (#10 adds them) → whichever of #10/#11 merges second must hand-update module list and count.
- Kakeya ZIP reached nobody via room; Jeremy to send in 1:1 to Lean Green. 7^5 question still open.
- 10:57 PM CST: ink 4a4a0c3 on #11 — dcube_cycles : SmallSupportsAreCycles dcubeE proved in kernel on v4.33.0 (328 split decide +kernel lemmas, propext + Quot.sound only, no symmetry, ~2.5 min; scripts/gen_tailfloor_dcube.py reproduces). Graph step now proved on all five graphs. Lean Green 7aaef43 adds TailFloorDoubleCube + OneLinkTailFloor to build/audit/gate (430 theorems, 372 frozen). Red's structural proof = later cleaner follow-up. #6 ready for Jeremy to merge. Open: SU(3) gauge support rule; per-link s; double-cube edge (0.5, 0.9867); 40/3, 43/3 in Lean; #10 config; Kakeya 7^5.
- 11:10 PM CST: #11 build setup done (7aaef43), waiting on CI only. Jeremy: "we dont need to stop."
- Spectrum draft proof of SU(3) gauge support rule (paper level, not Lean): Peter–Weyl, L²(SU(3)) = ⊕_R R⊗R*; gauge action at each end of a link acts inside each block, so the Gauss-law projector P = ⊗_v P_v commutes with the projector onto each irrep labelling {R_e}. Hence every gauge-invariant state is a sum of gauge-invariant states of definite labelling, and the electric term Σ C₂(R_e) is diagonal there. Fixed labelling: the vertex-v factor lives in Inv(⊗_{e∋v} R_e^{±}). (a) one nontrivial link at v: Inv(R)=0 for nontrivial irreducible R → no dangling link. (b) degree 2: Inv(R1^±⊗R2^±) ≅ Hom(R1^∓,R2^±) ≠ 0 iff isomorphic (Schur), dim 1 → irreps conjugate-matched along an oriented cycle (equal if consistently oriented). Lean route: Mathlib Representation/FDRep + Schur (FDRep.finrank_hom_simple_simple) for compact-group finite reps; Peter–Weyl for SU(3) not in Mathlib → keep the sector decomposition as hypothesis, formalize (a),(b) at finite-rep level.
- Spectrum check of GPT's two-plaquette (theta 1,3,3) tensor cases: script /workspace/colour-team/ym/theta/theta.py (+theta.out). SU(3) weights via Gelfand–Tsetlin, tensor products via Racah–Speiser (self-tests 3⊗3, 3⊗3̄, 8⊗8 pass); arm irreps A (short), B, C (long), invariant iff C̄ ⊂ A⊗B; all irreps p+q ≤ 6 (complete below 17). Energy levels: 16/3, 8, 28/3, 11, 34/3, 12, 40/3, 43/3, 46/3, 49/3, 17. Confirms: above 12 first is 40/3 (sextet square); above 40/3 first is 43/3 (short 3̄/3, long 8, long 3); trivial short arm gives 6·C2(B) = 8, 18, 20...; both long arms 3/3̄ give 28/3 (A=3), 11 (A=8), 34/3 (A=6). Assumes the gauge rule (one irrep per arm).
- 11:12 PM CST: Red final split — ink 40/3, 43/3 Lean (Spectrum's theta check is the vetted case list); Green double-cube edge; Grey varying s + frozen targets for general Schur lemmas (no invariants in single nontrivial simple rep; pair invariants nonzero iff dual, then dim 1); Red proves them; Peter–Weyl = one named assumption; Lean Green merges #11 (Jeremy said yes) then combined #10 fix (461 theorems, 383 frozen) and structural graph lemma.
- 11:13 PM CST: #11 merged → main 3c3be94 (tail floor layers 1+3 incl. double cube, 430 theorems gated). #10 next with Lean Green's combined fix.

## 11:34 PM CST round
- Red: T1 gauge_no_dangling, T2 gauge_pair_finrank proved on pinned v4.33.0 (branch red-gauge-support 0f152ac); two syntax-only freeze edits logged (ebfe57e). Open: vertex regrouping + support-predicate match; Peter–Weyl named assumption.
- ink: StructuralCore core_claim (bipartite + pair-free in K6, ≤6 links ⇒ single C4/C6); transfer/relabelling open. Correction: triangle-free insufficient (C5).
- Grey varying s: t exact. two squares 4/3, cube 7/9, double cube 7/15 (weighted mix of 19 thetas, not uniform), corner 10/9, strip 1 (settled, not 36/35). Strip and corner close in (5, 5.25]; λ=5 gap real for this bound (r ≥ P·g(c) is the lever). Green verified exactly at N=24 and N=28.
- Green double-cube wall edge (α=1): even split excluded from 1.7338256; c=20/11 (uniform over all splits) excluded from 1.7347717, not excluded at 1.7347412. GPT's 0.9867 is a different test (U(λ) vs retained-matrix min eigenvalue), definition/script not yet seen — unverified.
- Lean Green: #10 at 471de40 merges cleanly, 461 thm / 383 frozen, CI running.
- Dictionary note: "uniform over splits" edge 1.7347717 is a certificate statement, not the physical spectrum.

## Corrections pass (Red's request, 11:34 PM CST)
- Jensen two-halves bound: needs g concave AND nondecreasing in κ (Grey checked on grid). Excited side Σg((1−s)κ_p) ≤ P·g((1−s)c); retained side uses true r ≥ max_κ Σg(κ_p) = P·g(c). Green's λ=2 "flip" withdrawn: it used a split's own floor, not common r.
- Double cube, two separate tests: (a) window wall, uniform over splits, excluded from λ/α = 1.7347717 (even split alone from 1.7338256); (b) GPT's trial-state U(λ) vs retained-matrix min eigenvalue, 0.9867 — unverified, definition/script pending.
- Wording: double-cube t = 7/15 is a WEIGHTED mixture of 19 7-thetas (uniform over 28 gives 5/7). Strip t = 1 via 1/4 each on two 7-thetas, outer 8-cycle, end-square pair.
- Structural lemma hypotheses: bipartite + no two vertices share >2 neighbours (no K2,3). Triangle-free alone fails (C5).
- Frozen-statement syntax edits (FREEZE-LOG ebfe57e): V.ρ.invariants → Representation.invariants V.ρ; T2 needs `open scoped Classical in`. Syntax only, meaning unchanged.
- 11:35 PM CST: Red — 1.7347717 endpoint certificate suffices via WindowWallMono (no grid). Green rerunning even split at λ=2 with common r=P·g(c). Lean Green: gauge wiring local, 391 frozen; 40/3, 43/3 theta floors started (core Lean only).
- 11:42 PM CST: Green dcube_uniform endpoint cert at 1.7347717 (h=1e-5; formal h=1/1000 test from 1.7352404), in #6. Even-split λ=2 rerun with common r confirms Jensen ordering (flip was own-floor artefact). ink: StructuralSupport.small_support_is_cycle proved (Mathlib v4.33.0), bridge to SmallSupportsAreCycles open; PR awaits Jeremy go. Red: GaugeSupportLattice 18d65fc (vertex_no_dangling, vertex_two_valent, lattice_support_rule); hyps left: dual-of-simple simple (Green), vertex nonzero invariant/regrouping, Peter–Weyl. Lean Green: #10 CI green, awaits Jeremy merge; gauge wiring 481/403, T1/T2 moved into namespace (logged); ThetaFloor.lean proves 40/3, 43/3 (4 realizations each) and full level list ≤17 vs theta.out; vertex rule = BMW/BZ closed form, checked not derived.

## Jeremy 11:44 PM CST: three views (energy / phase / resonance) — sorting
- Physical: centre Z3 of SU(3) (triality); string tension; mass gap m = E1−E0 = −(1/a)log(t1/t0) of transfer matrix e^{−aH}.
- Ours: B35, B69 (digits/step = −log10|λ2/λ1|), B128, B193 twist floor, single-link pendulum √(2κλ).
- Caveat: pure gauge + Gauss law ⇒ every site singlet; nontrivial triality only as static external charges or as Z3 electric flux around a periodic direction ('t Hooft sectors). Our five supports are open graphs: flux sectors need periodic lattice or added charges.
- Resonance view must take λ2 inside zero-flux gauge-invariant sector, else it reads a flux (string) state.
- None run yet.

## B35 / B69 entry (Red's assignment, 11:44 PM CST). Source: relational-atlas-lean atlas/cards/html, local commit 172175e (2026-10-14); check against latest Zenodo before quoting externally.
- B35 "Phase crosses what amplitude cannot." Grade: measured (L3→L5). Content: crossing a rigidity wall, individual eigenprojectors diverge (|v⊥| ∝ 1/√(2λ)) while the block projector keeps Tr Π_blk = 2 exactly and the contour ledger evaluates cleanly at the defective point. Memory crosses as a phase and an integral, not a vector. YM use: analogy for "triality label survives where amplitudes don't" — ours, not a physics result.
- B69 "A gap predicts a rate, and picks the route." Grade: measured (L2→L0). Content: digits per step = −log10|λ2/λ1| of the limiting step operator (one 3×3 eigenvalue computation) predicts collapse to rank one of a cumulative transport product; 0.94% worst relative error over 8 directions (1.05–7.21 digits/step); 42 directions scored blind. Card's own caveats: lower-bound instrument, not optimality proof; predicts rank-one collapse, not direction convergence.
- YM translation: for T = e^{−aH}, −log10|t1/t0| = a(E1−E0)/ln10. Identical to the Hamiltonian gap (ink/Red/Green): independent only if measured from products/correlators, not from H's spectrum. Card's "rank-one collapse ≠ direction convergence" caveat maps to: decay of the projector onto the vacuum vs convergence of a chosen state — the latter can be slowed by small overlap.
