# Provenance

The original twelve Lean files are byte-identical copies of sources in the private `operator-first`
repository, taken from branch `formal/yang-mills-longest-chain-2026-09-13` at commit
`3eb82d5f5dd5`, which carries the union of the Yang–Mills lanes.
`SchurInertiaComparison.lean` is the new finite sign-transfer module written for this
public repository. Its exact proof status is determined by this repository's own CI.

The three direct positive-response declarations added to `CouplingFeedback.lean` on 28 September 2026 are adapted from the already-green finite theorem source `research/upg/formal/UPGPositiveFeedback.lean` at operator-first commit `c4e045d41642` (dedicated run 34866326919). They are restated in the existing `YangMillsFinite` namespace against this repository's `feedbackWith` definition; this repository's own CI is authoritative for the adapted source.

The complete `paper/2026-09-08/` directory is copied from the previously verified
`Yang_Mills_Continuation_2026-09-08.zip` (SHA-256
`3bd8f6872700931c6a22d2d8fa296b3579e56d9be37df5e3892140dfe6744f2a`).
The `research/yang_mills_2026_09_09/` tree comes from private research PR #18 at
`4c90eaa499cde0c178ac3378a2138aa8aa9c5c34`. These historical reports retain
their original dates and claims about where the full Compound Eye application was
delivered. This public repository carries the focused native reproduction.

| Files | Source directory | Earlier verification |
| :--- | :--- | :--- |
| `GaugeCertificates.lean`, `FalseControls/GaugeControl.lean` | `research/yang_mills_2026_09_09/lean/` | PR #18, commit `4c90eaa499cd` |
| `CrossTheorem`, `MatrixResolvedBoundary`, `FalseControls/CrossTheoremControl.lean` | `research/yang_mills_2026_09_09/cross_theorem/lean/` | PR #18; PR #27 (Actions run 34698115560) |
| `SchurCongruence`, `ProjectorKernel`, `CouplingFeedback`, `ObservabilityKernel`, `ProjectorDynamics` | same | PR #51 |
| `TailGapTransfer`, `SchurFloorTransfer`, `NonuniformAllocationFloor` | same | PRs #52, #54, #56 |
| `LongestYangMillsChain` | same | this branch |

PR #51 and #52 had failed dedicated runs at their respective old heads; PR #60
has a successful combined run at `3eb82d5f5dd5`. This repository's current
check is the certification of its own exact source. The SHA-256 of every checked
Lean file is written to `verification/report.json` on each run.
