<div align="center">

# Retained Geometry and Certified Gauge Cutoffs

**The Yang–Mills research record: the September 8 paper and verification scripts, the September 9 spatial calculations, and machine-checked finite algebra.**

[![Lean proof check](https://github.com/dicipler-pixel/yang-mills-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/yang-mills-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.33.0-blue)
![Theorems](https://img.shields.io/badge/theorems-832-2EA043)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
![Code: MIT](https://img.shields.io/badge/code-MIT-lightgrey)
![Text: CC BY 4.0](https://img.shields.io/badge/text-CC%20BY%204.0-lightgrey)

Jeromie Beasley, with the Grok Bot colour team (see [Credits](#credits))

[ORCID](https://orcid.org/0009-0006-4645-5643) · [GitHub dicipler-pixel](https://github.com/dicipler-pixel) · [X @d1c1pler](https://x.com/d1c1pler) · [YouTube @AtlasMemoriae](https://www.youtube.com/@AtlasMemoriae) · [Atlas Memoriae](https://atlas-memoriae.dicipler.workers.dev)

</div>

---

## The idea in one line

Keep the shape of the coupling to the discarded sector instead of its norm. Where a scalar norm
bound says nothing, the boundary-matrix Schur certificate returns a rigorous lower bound on the
untruncated one-loop gap. The paper gives the complete-tail argument; the Lean modules certify
specified finite algebra. The spatial work checks five original-link SU(3) models.

## Start here

| If you want to… | Open |
| :--- | :--- |
| Read the September 8 paper and reproduce the frame, holonomy and one-loop results | [Paper and source bundle](paper/2026-09-08/) |
| Rebuild the five spatial models and 58 rational targets | [September 9 research report](research/yang_mills_2026_09_09/cross_theorem/REPORT.md) and [native reproduction](research/yang_mills_2026_09_09/cross_theorem/native/) |
| Check the Schur inertia argument and formalization boundary | [Schur inertia bridge](SCHUR_INERTIA_BRIDGE.md) |
| Describe the result relative to established full-operator methods | [Prior art and scope](PRIOR_ART_AND_SCOPE.md) |
| Know exactly what is **not** proved | [`LIMITATIONS.md`](LIMITATIONS.md) |
| Check where every file came from | [`PROVENANCE.md`](PROVENANCE.md) |
| See the statements that must be rejected | [`FalseControls/`](FalseControls/) |

## What the library contains

| Subject | File | Theorems |
| :--- | :--- | :-: |
| **Gauge certificates**: exact LDLᵀ factorizations and pivot signs for the inner 10×10 and outer 7×7 matrices of the two-plaquette (shared-link) SU(3) certificate, plus exact arithmetic of its displayed cutoff constants. Haar integration, basis completeness, the analytic tail and Sylvester inertia are written proofs | [`GaugeCertificates`](GaugeCertificates.lean) | 21 |
| **Cross theorem**: the scalar closing kernel; four of the twelve are exact arithmetic for the 45-state cube constants | [`CrossTheorem`](CrossTheorem.lean) | 12 |
| **Matrix-resolved boundary**: the boundary coupling kept as a matrix, not a norm | [`MatrixResolvedBoundary`](MatrixResolvedBoundary.lean) | 5 |
| **Schur congruence**: the block congruence behind the certificate | [`SchurCongruence`](SchurCongruence.lean) | 3 |
| **Projector kernel**, **coupling feedback**, **observability kernel**, **projector dynamics**: from the adapted projector commutator to retained–hidden feedback and what an observation can see | [`ProjectorKernel`](ProjectorKernel.lean), [`CouplingFeedback`](CouplingFeedback.lean), [`ObservabilityKernel`](ObservabilityKernel.lean), [`ProjectorDynamics`](ProjectorDynamics.lean) | 17 |
| **Tail-gap transfer**, **Schur floor transfer**, **nonuniform allocation floor**: scalar bookkeeping for nonuniform, overlapping hidden-tail budgets and local floors, and the finite Schur-complement equivalence for positivity above a candidate floor | [`TailGapTransfer`](TailGapTransfer.lean), [`SchurFloorTransfer`](SchurFloorTransfer.lean), [`NonuniformAllocationFloor`](NonuniformAllocationFloor.lean) | 12 |
| **Combined lanes**: three finite lanes in one file, not composed into a single implication. (i) A vanishing projector commutator forces zero coupling, zero feedback and no Schur correction; the transported projector's tangent is the commutator, and half its cross-block energy and the feedback trace both equal the coupling energy. (ii) For positive-semidefinite residues with positive denominators: if the retained block clears the common-floor penalty, the energy-resolved comparison lies below the Schur complement (`K_res ≤ S`, assumed) and the shifted hidden block is positive definite, then the full shifted block is positive semidefinite. (iii) Scalar overlap-allocation bookkeeping leaves a positive residual. A dual observability certificate survives any invertible change of coordinates | [`LongestYangMillsChain`](LongestYangMillsChain.lean) | 7 |
| **Schur sign comparison**: positive subspaces and negative trial directions transfer through ordered finite matrices | [`SchurInertiaComparison`](SchurInertiaComparison.lean) | 2 |
| **Finite inertia count**: positive codimension-one and negative one-dimensional subspaces give exactly one negative direction and no radical | [`SchurInertiaCount`](SchurInertiaCount.lean) | 1 |
| **Window wall**: the window function W(s), its derivative and finite (derivative-free) bounds, monotonicity in the coupling (an exclusion carries to every larger λ), the certified cells, and the split-free two-halves Jensen bound | [`WindowWall`](WindowWall.lean), [`WindowWallDeriv`](WindowWallDeriv.lean), [`WindowWallFinite`](WindowWallFinite.lean), [`WindowWallMono`](WindowWallMono.lean), [`WindowWallCells`](WindowWallCells.lean), [`WindowWallJensen`](WindowWallJensen.lean) | 37 |
| **Tail floor**: the 28/3 electric tail floor (layers 1 and 3), the one-link SU(3) tail floor, and the kernel-checked double-cube support check (328 lemmas) | [`TailFloor`](TailFloor.lean), [`OneLinkTailFloor`](OneLinkTailFloor.lean), [`TailFloorDoubleCube`](TailFloorDoubleCube.lean) | 350 |
| **Small supports are cycles**: on a bipartite graph where no two vertices share three neighbours, a support with at most 6 links and minimum degree 2 is a single 4- or 6-cycle, proved in general with no search | [`SmallSupportCycle`](SmallSupportCycle.lean) | 6 |
| **Small support bridge**: list supports relabelled as simple graphs (list degree = graph degree, link count = edge count, graph connectivity makes the list checker pass), giving `SmallSupportsAreCycles` on any simple host link list with a two-colouring and at most two common neighbours per vertex pair. The five test graphs, the double cube included, then follow from a colouring and codegree check alone; `K_{2,3}` fails the codegree check. Graph-theoretic Layer 3 only: the gauge support rule (Layer 2) stays open | [`SmallSupportBridge`](SmallSupportBridge.lean) | 27 |
| **Gauge support rule**: Schur at each vertex, no dangling link (`gauge_no_dangling`), paired irreps on two-link vertices (`gauge_pair_finrank`), the per-vertex and lattice rule, and the dual of a simple representation is simple (`dual_simple`). Regrouped by vertex (`gauge_support_rule_regrouped`, `_SU3`): a nonzero gauge-invariant vector of ⊗_v W_v forces a nonzero invariant at every vertex, so every labelling in the support of a gauge-invariant state obeys the lattice rule with no per-vertex hypothesis. Still assumed, as the named hypothesis `PeterWeylSU3` (a structure, not an axiom): Peter–Weyl link by link together with the reshuffle ⊗_e (V ⊗ V*) ≅ ⊗_v W_v | [`GaugeSupport`](GaugeSupport.lean), [`GaugeSupportFDRep`](GaugeSupportFDRep.lean), [`GaugeSupportLattice`](GaugeSupportLattice.lean), [`DualSimple`](DualSimple.lean), [`GaugeSupportRegroup`](GaugeSupportRegroup.lean) | 44 |
| **Theta floors and triality**: SU(3) levels on the (1,3,3) theta graph, the 40/3 and 43/3 floors, triality conserved at singlet vertices, and the transfer-gap identity (an algebraic identity, not independent evidence) | [`ThetaFloor`](ThetaFloor.lean), [`ThetaTriality`](ThetaTriality.lean), [`TransferGap`](TransferGap.lean) | 39 |
| **Cut bound**: any SU(3) irrep with nonzero triality has Casimir at least 4/3, so d such cuts cost at least (4/3)·d, and d copies of the 3 attain it. That each cut carries nonzero triality is assumed, not derived from Gauss's law | [`CutBound`](CutBound.lean) | 5 |
| **Ky Fan chord**: if E₀+E₁ is concave in κ (Ky Fan's theorem for an H linear in κ, taken as a hypothesis), certified lower bounds at the chord ends and an affine upper bound on E₀ give a lower bound on the gap across the interval. The exact node values are in [`research/2026-11-11/kyfan_chord`](research/2026-11-11/kyfan_chord/) | [`KyFanChord`](KyFanChord.lean) | 4 |
| **Triality at an n-valent vertex**: if the centre element acts on every arm by ω^triality (a named hypothesis `CentreCharacter`, the SU(3) centre fact, not proved here) and the vertex space has a nonzero invariant, the signed trialities sum to 0 mod 3 at any valence, with incoming arms entering as conjugates; also as zero net flux in ℤ/3. The one-, two- and three-valent cases follow as corollaries, and the closed singlet formula is shown to agree | [`TrialityVertex`](TrialityVertex.lean) | 20 |
| **SU(3) centre character**: in Mathlib's `specialUnitaryGroup (Fin 3) ℂ`, ω·I is in SU(3) and acts on 3 by ω, on 3̄ by ω², on 3^{⊗p} ⊗ 3̄^{⊗q} by ω^triality(p,q), and the same on every subrepresentation. This discharges `CentreCharacter`, so triality conservation at an n-valent vertex holds unconditionally for arms that embed in these tensor representations. The embedding of the genuine irrep (p,q) into 3^{⊗p} ⊗ 3̄^{⊗q} is not formalized | [`CentreCharacterSU3`](CentreCharacterSU3.lean) | 17 |
| **SU(3) highest-weight embedding**: V(p,q) is defined as the subrepresentation of 3^{⊗p} ⊗ 3̄^{⊗q} generated by e₁^{⊗p} ⊗ e₃*^{⊗q}. It is a nonzero subrep with a mono into the tensor power, its generator is a torus weight vector of weight (p,q), its centre character is ω^((p+2q) mod 3), the triality label is forced (V(1,1) does not embed in 3 ⊗ 3), and n-valent triality holds for arms isomorphic to V(p,q). Irreducibility of V(p,q) and the highest-weight classification are not formalized | [`IrrepEmbedSU3`](IrrepEmbedSU3.lean) | 23 |
| **ThetaFloor triality from the centre character**: the triality ThetaFloor attaches to the label (p,q) is exactly the exponent by which ω·I acts on V(p,q), and the only one in {0,1,2}; V(p,q) carries the swapped label's triality only when it is 0. `hasSinglet` splits as vanishing vertex triality plus the BMW inequalities, and the triality clause is proved from `nvalent_triality_irrepRep` for V(a), V(b), V(c) arms with a nonzero invariant, at both theta vertices. Every entry of the theta tables (34 rows, level 40/3, level 43/3) satisfies the proved condition, and swapping p ↔ q on an arm of nonzero triality breaks it. `cas3` is blind to p ↔ q and cas3 ≡ triality² (mod 3), so the level is an integer iff the short arm has triality 0. That `cas3` and the BMW inequalities are the Casimir and tensor rule of V(p,q) needs irreducibility and is not claimed | [`ThetaFloorTriality`](ThetaFloorTriality.lean) | 23 |
| **Explicit SU(3) singlets: the smallest theta rows are attained**: Σᵢ eᵢ ⊗ eᵢ* in 3 ⊗ 3̄ (from g g⁻¹ = 1), ε = Σ ε_{ijk} eᵢ ⊗ eⱼ ⊗ e_k in 3 ⊗ 3 ⊗ 3 (from det g = 1, via Σ ε_{ijk} g_{ai} g_{bj} g_{ck} = det g · ε_{abc}) and its dual in 3̄ ⊗ 3̄ ⊗ 3̄ (from det (g⁻¹)ᵀ = 1) are each nonzero and SU(3)-invariant. So the eight theta-table rows with arms in {1, 3, 3̄} — the six orderings of (1, 3̄, 3), (3, 3, 3) and (3̄, 3̄, 3̄) — have a nonzero invariant at both theta vertices: attained, not only allowed. The same ε placed in 3 ⊗ 3 ⊗ 3̄ is scaled by ω under ω·I and is not invariant; 3 ⊗ 3 ⊗ 3̄ has no invariant at all. The arms are 3, 3̄, 1 themselves; `IrrepSmallIsoSU3` identifies them with V(1,0), V(0,1), V(0,0) | [`SingletWitnessSU3`](SingletWitnessSU3.lean) | 45 |
| **V(1,0) ≅ 3, V(0,1) ≅ 3̄, V(0,0) ≅ 1**: the cyclic permutation matrix (det +1, orthogonal) is in SU(3) and its orbit moves e₁ through the whole standard basis of 3 and e₃* through the whole dual basis of 3̄, so the subrepresentations V(1,0), V(0,1), V(0,0) of #30 are all of 3 ⊗ 1, 3̄ ⊗ 1, 1, and the inclusion followed by the right unitor gives explicit FDRep isomorphisms `irrep10Iso`, `irrep01Iso`, `irrep00Iso` (highest-weight vector to e₁, e₃*, 1). V(0,1) is not isomorphic to 3: ω·I acts by ω² on one and ω on the other, so 3̄ ≇ 3 and V(1,0) ≇ V(0,1). Transported along the isomorphisms, the trace and ε witnesses live on V(1,0) ⊗ V(0,1), V(1,0)^{⊗3}, V(0,1)^{⊗3}, and the eight attained theta rows have a nonzero invariant at both vertices with arms V(a), V(b), V(c): for these rows both directions of the singlet rule hold on the same objects | [`IrrepSmallIsoSU3`](IrrepSmallIsoSU3.lean) | 34 |
| **Gauge supports as list supports**: the non-trivial links of a labelling, read as a TailFloor link list, have list degree equal to the number of non-trivial half-edges in `ntList` at each vertex. So the regrouped gauge support rule makes every support of a gauge-invariant state `admissible`, with degree at least 2 at every touched vertex. On a simple, two-coloured, codegree-≤2 host, supports with at most six links are single 4- or 6-cycles. Still under the named hypothesis `PeterWeylLattice`; `K_{2,3}` is admissible but not a cycle | [`NtListSupport`](NtListSupport.lean) | 12 |
| **List order and the cube**: `deg`, vertex membership, `admissible`, and (onto a list with no loops and no repeated link) `connected` and `shortCycle` are unchanged by reordering links. Every sublist of a host with 1 to 6 links is enumerated by `smallSupports`, so a gauge support's host-ordered copy is one of the supports `SmallSupportsAreCycles g` covers. On the cube (`cubeΓ`, link i = i-th pair of `cubeE`), every labelling in the support of a gauge-invariant state with 1 to 6 non-trivial links is a 4- or 6-cycle, under the named hypothesis `PeterWeylLattice` alone | [`PermCube`](PermCube.lean) | 23 |
| **Graph instances**: the `cubeΓ` pattern made generic (`listΓ g n`, link i = i-th pair of the TailFloor edge list, `lab = Fin.val`) and applied to the two squares, the three-square strip, the corner and the double cube. Under the named hypothesis `PeterWeylLattice` alone, every labelling in the support of a gauge-invariant state with 1 to 6 non-trivial links is a 4- or 6-cycle, so it has exactly 4 or 6 non-trivial links. The double cube uses #23's colouring-and-codegree route, with no support enumeration | [`GraphInstances`](GraphInstances.lean) | 25 |
| **Short or long**: one statement per graph (cube, two squares, strip, corner, double cube, and generic `listΓ`). For a nonzero gauge-invariant component with at least one non-trivial link, under `PeterWeylLattice` alone, either it has 4 or 6 non-trivial links forming a short cycle, or more than 6 and the conclusion of `long_support_floor` holds (any 7+ link costs, each at least 4, sum to at least 28 in `c3` units). `long_energy_floor` gives that bound for Dynkin labels, assuming a non-trivial link has a nonzero label | [`SupportDichotomy`](SupportDichotomy.lean) | 9 |
| **Labels on links**: with link irreps indexed by Dynkin label, `irr (p,q) = V(p,q)`, a link is non-trivial exactly when its label is not (0,0). (0,0) is trivial by `irrep00Iso`. Any other V(p,q) is not trivial because a torus element diag(t, t̄, 1) or diag(1, t, t̄), with t a primitive root of unity, moves the highest-weight vector by tᵖ or t^q ≠ 1. So `long_energy_floor` holds with no labelling hypothesis: more than six non-trivial links cost Σ c3 ≥ 28. The dichotomy with that energy floor still assumes each V(p,q) is simple (irreducibility is not formalized) | [`HntLabels`](HntLabels.lean) | 9 |
| | **Total** | **832** |

Among the first 80 theorems, besides the matrix factorizations, fifteen are exact arithmetic checks of
displayed rational constants: eleven in `GaugeCertificates` and four in `CrossTheorem`.

## How it is checked

Every push runs [the proof check](.github/workflows/build.yml) on GitHub. The paper's
Python verifiers are separate and run from the research folders:

1. **Build**: every module compiles against Lean v4.33.0 and Mathlib `v4.33.0`.
2. **Independent replay**: every module is re-checked by Lean's separate kernel checker.
3. **Axiom audit**: every named theorem depends only on `propext`, `Classical.choice` and
   `Quot.sound`. No `sorry`, no project axioms, no `native_decide`.
4. **False controls**: twenty-seven false statements in [`FalseControls/`](FalseControls/) must be
   rejected, showing the checker says no. Two are plain arithmetic (`(2 : ℚ) = 3` and
   `(1 : ℚ)/2 ≤ 1/3`); the other twenty-five are near-miss versions of the window-wall cells, Jensen bound,
   dual-simple, theta floor, triality, transfer-gap, cut-bound and Ky Fan chord statements, and
   two-, three- and four-valent vertex labellings whose trialities do not sum to 0, and the
   adjoint 8 inside 3 ⊗ 3̄ claimed to have triality 1, and the adjoint V(1,1) claimed to carry the
   triality 2 of 3 ⊗ 3, and a theta-table row (1, 3̄, 3) with the 3̄ arm's triality swapped p ↔ q,
   and the Levi-Civita tensor ε claimed SU(3)-invariant in 3 ⊗ 3 ⊗ 3̄, and V(0,1) claimed isomorphic to 3,
   the three regrouped gauge-support statements, a support with a degree-one vertex claimed admissible, `K_{2,3}` claimed to be a short cycle, a reordered support claimed to change a degree, a 5-link double-cube support claimed to be a short cycle, a 3-link strip support claimed to be a short cycle, and a link labelled (0,0) claimed non-trivial.
5. **Frozen statements**: 745 theorem statements are frozen, so a proof cannot pass by quietly
   weakening what it proves. Every edit to a frozen statement is logged.

```bash
lake exe cache get
lake build
python3 scripts/verify.py
```

## Named open items

- **Irreducibility of V(p,q).** `IrrepEmbedSU3` defines V(p,q) as the subrepresentation of
  3^{⊗p} ⊗ 3̄^{⊗q} generated by e₁^{⊗p} ⊗ e₃*^{⊗q}, but does not prove it irreducible (that needs
  the raising operators and Weyl's theorem). Until it is, ThetaFloor's `cas3` and the BMW part of
  `hasSinglet` are label arithmetic, not proved properties of V(p,q); only the triality part is
  proved for V(p,q) (`ThetaFloorTriality`).
- **Classification of SU(3) irreps.** That every irreducible SU(3) representation is isomorphic
  to some V(p,q) is not formalized, so the triality results cover arms given as V(p,q) up to
  isomorphism.
- **Sufficiency of the singlet rule.** The smallest rows are attained by explicit witness
  (`SingletWitnessSU3`): the trace invariant of 3 ⊗ 3̄ and ε, ε* of 3 ⊗ 3 ⊗ 3 and 3̄ ⊗ 3̄ ⊗ 3̄ give a
  nonzero invariant at both vertices of the eight theta rows with arms in {1, 3, 3̄}. The general
  converse, that the BMW inequalities plus vanishing triality give a nonzero invariant of
  V(a) ⊗ V(b) ⊗ V(c) for every admissible row, is not formalized. The identification of
  3, 3̄, 1 with V(1,0), V(0,1), V(0,0) is done (`IrrepSmallIsoSU3`), so those eight rows are
  attained on the V(p,q) arms themselves; for larger (p,q) the arms are not yet matched to a
  concrete model.

## The paper

The [September 8 paper](paper/2026-09-08/YANG_MILLS_CONTINUATION.pdf) is a dated
snapshot. Later spatial calculations and Lean modules extend it. No revised combined
manuscript or four-dimensional continuum mass gap is claimed here.

## Credits

This library is Jeromie Beasley's research, and the November 2026 additions were a full team
effort. The research questions, the physics and the direction are Jeromie's. The Lean modules
and certificates added from 2026-11-09 to 2026-11-11 were built with his team of Grok Bot
assistants, each working in the open in this repository:

- **Red** led the Yang–Mills Lean work and set the merge order; wrote the gauge support rule
  (`GaugeSupport`, `GaugeSupportFDRep`, `GaugeSupportLattice`) and the resonance cross-check.
- **Green** proved the derivative/secant window wall, the one-link tail floor, the split-free
  Jensen bound (`WindowWallJensen`) and `dual_simple` (`DualSimple`), certified the Ky Fan chord
  gap on the one plaquette and the two-square cell, and certified the 58 windows,
  the λ = 5 slope endpoints and the double-cube uniform endpoint.
- **Lean Green PR Machine** proved the certified-point window wall, `WindowWallMono`, `ThetaFloor`,
  `ThetaTriality`, `TransferGap`, `CutBound`, `KyFanChord`, `TrialityVertex`, `CentreCharacterSU3`, `SmallSupportBridge`, `NtListSupport`, `PermCube`, `GraphInstances`, `SupportDichotomy` and `HntLabels`, wired the gauge modules into the gate, and cross-checked the
  λ = 5 strip and corner slopes in exact rationals.
- **ink between the stars** built the 28/3 tail floor and its kernel-checked double-cube check
  (`TailFloor`, `TailFloorDoubleCube`) and proved the general small-support lemma
  (`SmallSupportCycle`).
- **Grey** wrote the frozen targets for the gauge support rule and the varying-s and string-floor
  scripts.
- **Spectrum** kept the team's dictionary of physical quantities versus our constructions, and
  wrote the SU(3) theta enumeration behind ThetaFloor's vetted list, and proved `IrrepEmbedSU3`, `ThetaFloorTriality`, `SingletWitnessSU3` and `IrrepSmallIsoSU3`.
- **Claude**, in Jeromie's sessions, wrote the window-wall cells module, the audit and the
  window-wall write-up, and carried out the final merge.

GPT reviewed the gate rules (log frozen-statement edits, never quietly drop a hard part, only
pinned-version CI counts). Every result above is checked by the Lean kernel, not by anyone's
say-so.

## Citation, licence and AI use

Citation metadata is in [`CITATION.cff`](CITATION.cff). The Lean code and scripts are released under the [MIT License](LICENSE) and the written text under [CC BY 4.0](LICENSE-CC-BY-4.0.md); see [`LICENSING.md`](LICENSING.md). How AI tools were used is stated in [`AI_USE.md`](AI_USE.md).
