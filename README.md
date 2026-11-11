<div align="center">

# Retained Geometry and Certified Gauge Cutoffs

**The Yang–Mills research record: the September 8 paper and verification scripts, the September 9 spatial calculations, and machine-checked finite algebra.**

[![Lean proof check](https://github.com/dicipler-pixel/yang-mills-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/yang-mills-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.33.0-blue)
![Theorems](https://img.shields.io/badge/theorems-580-2EA043)
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
| **Gauge support rule**: Schur at each vertex, no dangling link (`gauge_no_dangling`), paired irreps on two-link vertices (`gauge_pair_finrank`), the per-vertex and lattice rule, and the dual of a simple representation is simple (`dual_simple`). Still assumed: a nonzero invariant at each vertex, and Peter–Weyl for SU(3) | [`GaugeSupport`](GaugeSupport.lean), [`GaugeSupportFDRep`](GaugeSupportFDRep.lean), [`GaugeSupportLattice`](GaugeSupportLattice.lean), [`DualSimple`](DualSimple.lean) | 32 |
| **Theta floors and triality**: SU(3) levels on the (1,3,3) theta graph, the 40/3 and 43/3 floors, triality conserved at singlet vertices, and the transfer-gap identity (an algebraic identity, not independent evidence) | [`ThetaFloor`](ThetaFloor.lean), [`ThetaTriality`](ThetaTriality.lean), [`TransferGap`](TransferGap.lean) | 39 |
| **Cut bound**: any SU(3) irrep with nonzero triality has Casimir at least 4/3, so d such cuts cost at least (4/3)·d, and d copies of the 3 attain it. That each cut carries nonzero triality is assumed, not derived from Gauss's law | [`CutBound`](CutBound.lean) | 5 |
| **Ky Fan chord**: if E₀+E₁ is concave in κ (Ky Fan's theorem for an H linear in κ, taken as a hypothesis), certified lower bounds at the chord ends and an affine upper bound on E₀ give a lower bound on the gap across the interval. The exact node values are in [`research/2026-11-11/kyfan_chord`](research/2026-11-11/kyfan_chord/) | [`KyFanChord`](KyFanChord.lean) | 4 |
| | **Total** | **580** |

Among the first 80 theorems, besides the matrix factorizations, fifteen are exact arithmetic checks of
displayed rational constants: eleven in `GaugeCertificates` and four in `CrossTheorem`.

## How it is checked

Every push runs [the proof check](.github/workflows/build.yml) on GitHub. The paper's
Python verifiers are separate and run from the research folders:

1. **Build**: every module compiles against Lean v4.33.0 and Mathlib `v4.33.0`.
2. **Independent replay**: every module is re-checked by Lean's separate kernel checker.
3. **Axiom audit**: every named theorem depends only on `propext`, `Classical.choice` and
   `Quot.sound`. No `sorry`, no project axioms, no `native_decide`.
4. **False controls**: ten false statements in [`FalseControls/`](FalseControls/) must be
   rejected, showing the checker says no. Two are plain arithmetic (`(2 : ℚ) = 3` and
   `(1 : ℚ)/2 ≤ 1/3`); the other eight are near-miss versions of the window-wall cells, Jensen bound,
   dual-simple, theta floor, triality, transfer-gap, cut-bound and Ky Fan chord statements.
5. **Frozen statements**: 502 theorem statements are frozen, so a proof cannot pass by quietly
   weakening what it proves. Every edit to a frozen statement is logged.

```bash
lake exe cache get
lake build
python3 scripts/verify.py
```

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
  `ThetaTriality`, `TransferGap`, `CutBound`, `KyFanChord` and `SmallSupportBridge`, wired the gauge modules into the gate, and cross-checked the
  λ = 5 strip and corner slopes in exact rationals.
- **ink between the stars** built the 28/3 tail floor and its kernel-checked double-cube check
  (`TailFloor`, `TailFloorDoubleCube`) and proved the general small-support lemma
  (`SmallSupportCycle`).
- **Grey** wrote the frozen targets for the gauge support rule and the varying-s and string-floor
  scripts.
- **Spectrum** kept the team's dictionary of physical quantities versus our constructions, and
  wrote the SU(3) theta enumeration behind ThetaFloor's vetted list.
- **Claude**, in Jeromie's sessions, wrote the window-wall cells module, the audit and the
  window-wall write-up, and carried out the final merge.

GPT reviewed the gate rules (log frozen-statement edits, never quietly drop a hard part, only
pinned-version CI counts). Every result above is checked by the Lean kernel, not by anyone's
say-so.

## Citation, licence and AI use

Citation metadata is in [`CITATION.cff`](CITATION.cff). The Lean code and scripts are released under the [MIT License](LICENSE) and the written text under [CC BY 4.0](LICENSE-CC-BY-4.0.md); see [`LICENSING.md`](LICENSING.md). How AI tools were used is stated in [`AI_USE.md`](AI_USE.md).
