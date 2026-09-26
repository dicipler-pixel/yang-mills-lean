<div align="center">

# Retained Geometry and Certified Gauge Cutoffs — Lean proofs

**Machine-checked finite algebra behind the Yang–Mills strand: gauge-cutoff certificates, the boundary-matrix Schur certificate, and the longest finite chain from projector geometry to an allocation floor.**

[![Lean proof check](https://github.com/dicipler-pixel/yang-mills-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/yang-mills-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.33.0-blue)
![Theorems](https://img.shields.io/badge/theorems-77-2EA043)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
![License](https://img.shields.io/badge/License-MIT-lightgrey)

Jeromie Beasley

</div>

---

## The idea in one line

Keep the shape of the coupling to the discarded sector instead of its norm. Where a scalar norm
bound says nothing, the boundary-matrix Schur certificate returns a rigorous lower bound on the
untruncated spectrum. These modules prove the finite algebra those certificates rest on.

## Start here

| If you want to… | Open |
| :--- | :--- |
| Know exactly what is **not** proved | [`LIMITATIONS.md`](LIMITATIONS.md) |
| Check where every file came from | [`PROVENANCE.md`](PROVENANCE.md) |
| See the statements that must be rejected | [`FalseControls/`](FalseControls/) |

## What the library contains

| Subject | File | Theorems |
| :--- | :--- | :-: |
| **Gauge certificates**: spatial gap estimates and certified cutoffs | [`GaugeCertificates`](GaugeCertificates.lean) | 21 |
| **Cross theorem**: the scalar closing kernel | [`CrossTheorem`](CrossTheorem.lean) | 12 |
| **Matrix-resolved boundary**: the boundary coupling kept as a matrix, not a norm | [`MatrixResolvedBoundary`](MatrixResolvedBoundary.lean) | 5 |
| **Schur congruence**: the block congruence behind the certificate | [`SchurCongruence`](SchurCongruence.lean) | 3 |
| **Projector kernel**, **coupling feedback**, **observability kernel**, **projector dynamics**: from the adapted projector commutator to retained–hidden feedback and what an observation can see | [`ProjectorKernel`](ProjectorKernel.lean), [`CouplingFeedback`](CouplingFeedback.lean), [`ObservabilityKernel`](ObservabilityKernel.lean), [`ProjectorDynamics`](ProjectorDynamics.lean) | 17 |
| **Tail-gap transfer**, **Schur floor transfer**, **nonuniform allocation floor**: how a hidden-tail gap and a local floor pass through the Schur complement | [`TailGapTransfer`](TailGapTransfer.lean), [`SchurFloorTransfer`](SchurFloorTransfer.lean), [`NonuniformAllocationFloor`](NonuniformAllocationFloor.lean) | 12 |
| **Longest chain**: the certified finite lanes recombined, geometry → coupling → feedback → floor | [`LongestYangMillsChain`](LongestYangMillsChain.lean) | 7 |
| | **Total** | **77** |

## How it is checked

Every push runs [the proof check](.github/workflows/build.yml) on GitHub:

1. **Build**: every module compiles against Lean v4.33.0 and Mathlib `v4.33.0`.
2. **Independent replay**: every module is re-checked by Lean's separate kernel checker.
3. **Axiom audit**: every named theorem depends only on `propext`, `Classical.choice` and
   `Quot.sound`. No `sorry`, no project axioms, no `native_decide`.
4. **False controls**: two arithmetic controls must be rejected, showing the checker says no.

```bash
lake exe cache get
lake build
python3 scripts/verify.py
```

## The paper

*Retained Geometry and Certified Gauge Cutoffs*, Jeromie Beasley. The Zenodo DOI will be added
here once the paper is deposited.

## Citation, licence and AI use

Citation metadata is in [`CITATION.cff`](CITATION.cff). The Lean code and scripts are released
under the [MIT License](LICENSE). How AI tools were used is stated in [`AI_USE.md`](AI_USE.md).
