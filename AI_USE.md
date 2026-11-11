# AI use

The research questions and the physics behind this library are Jeromie
Beasley's. AI tools (Claude and ChatGPT) were used to search the literature,
write and repair Lean proofs, and organise this repository.

No statement here rests on an AI's say-so. Every proof is checked by the Lean
kernel and replayed by an independent kernel checker on every push, every
theorem's axioms are audited, and every false control must be rejected for the
check to pass. What the statements mean, and what they do not claim, is set
out in plain words in `README.md` and `LIMITATIONS.md`.

## This revision (2026-11-11)

The merge of the seven open pull requests (#10, #13, #12, #15, #16, #14 and
#6, in that order) was carried out by an agent working in this environment, at
Jeromie's instruction. Three of the seven conflicted on the audit registries —
`lakefile.toml`, `scripts/config.json` and `scripts/frozen_statements.json` —
and the conflicts were resolved by taking the union of the module roots, the
module entries and the frozen statements, and recomputing the theorem count
from the sources rather than accepting any branch's stated number. No frozen
statement's text differed between the two sides, so that resolution settled no
question about the mathematics.

The merged tree was checked before it was pushed: all 31 modules elaborate, the
inventory is 544 theorems, `#print axioms` over all 544 returns only `propext`,
`Classical.choice` and `Quot.sound`, all eight false controls are rejected for a
mathematical reason, and the token and statement-parity gate passes on 466
frozen statements. That run used the toolchain installed in this environment
(Lean 4.33.1) rather than the pinned 4.33.0, so it supplements the CI run on the
pin; it does not replace it.

A separate exercise during the same session, by a set of identical agents
working from published task statements, produced review material on Layer 2 of
the tail floor — the gauge support rule. None of it is asserted in this
library: nothing there is formalised, and any change to `SPATIAL_BASES.md`,
`GAUGE_SUPPORT_RULE.md` or `LIMITATIONS.md` that follows from it will be
committed and reviewed on its own, with the disagreement between the two
treatments stated rather than resolved silently.
