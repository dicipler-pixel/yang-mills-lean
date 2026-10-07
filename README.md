<div align="center">

# Retained Geometry and Certified Gauge Cutoffs

**The Yang–Mills research record: the September 8 paper and verification scripts, the September 9 spatial calculations, and machine-checked finite algebra.**

[![Lean proof check](https://github.com/dicipler-pixel/yang-mills-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/yang-mills-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.33.0-blue)
![Theorems](https://img.shields.io/badge/theorems-79-2EA043)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
![Code: MIT](https://img.shields.io/badge/code-MIT-lightgrey)
![Text: CC BY 4.0](https://img.shields.io/badge/text-CC%20BY%204.0-lightgrey)

Jeromie Beasley

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
| | **Total** | **79** |

Besides the matrix factorizations, fifteen of the 79 theorems are exact arithmetic checks of
displayed rational constants: eleven in `GaugeCertificates` and four in `CrossTheorem`.

## How it is checked

Every push runs [the proof check](.github/workflows/build.yml) on GitHub. The paper's
Python verifiers are separate and run from the research folders:

1. **Build**: every module compiles against Lean v4.33.0 and Mathlib `v4.33.0`.
2. **Independent replay**: every module is re-checked by Lean's separate kernel checker.
3. **Axiom audit**: every named theorem depends only on `propext`, `Classical.choice` and
   `Quot.sound`. No `sorry`, no project axioms, no `native_decide`.
4. **False controls**: two arithmetic controls, `(2 : ℚ) = 3` and `(1 : ℚ)/2 ≤ 1/3`, must be
   rejected, showing the checker says no. They do not involve the Yang–Mills definitions.

```bash
lake exe cache get
lake build
python3 scripts/verify.py
```

## The paper

The [September 8 paper](paper/2026-09-08/YANG_MILLS_CONTINUATION.pdf) is a dated
snapshot. Later spatial calculations and Lean modules extend it. No revised combined
manuscript or four-dimensional continuum mass gap is claimed here.

## Citation, licence and AI use

Citation metadata is in [`CITATION.cff`](CITATION.cff). The Lean code and scripts are released under the [MIT License](LICENSE) and the written text under [CC BY 4.0](LICENSE-CC-BY-4.0.md); see [`LICENSING.md`](LICENSING.md). How AI tools were used is stated in [`AI_USE.md`](AI_USE.md).
