# FREEZE-LOG: gauge support targets (GaugeSupportFDRep.lean)

Targets drafted by Grey, proved by Red on 2026-11-10 on Lean v4.33.0 / Mathlib v4.33.0.
The mathematical content of both statements is unchanged. Two syntax fixes were needed
for them to typecheck.

## Fix 1: `V.ρ.invariants` (T1 and T2)

- **Before:** `V.ρ.invariants = ⊥` and `finrank k (Vᘁ ⊗ W).ρ.invariants = ...`
- **After:** `Representation.invariants V.ρ = ⊥` and
  `finrank k (Representation.invariants (Vᘁ ⊗ W).ρ) = ...`
- **Reason:** `FDRep.ρ` has type `G →* (V →ₗ[k] V)`, which is not syntactically
  `Representation k G V`, so dot notation fails: "Invalid field `invariants`: The environment
  does not contain `MonoidHom.invariants`". Writing the function name explicitly is the same
  term. The parentheses in T2 are needed because `finrank k` now takes one explicit argument.

## Fix 2: `open scoped Classical in` before T2

- **Before:** the theorem with no surrounding `open`.
- **After:** `open scoped Classical in` placed before `theorem gauge_pair_finrank`.
- **Reason:** `if Nonempty (V ≅ W) then 1 else 0` needs a `Decidable (Nonempty (V ≅ W))`
  instance ("failed to synthesize instance Decidable (Nonempty (V ≅ W))"). Mathlib's own
  `FDRep.finrank_hom_simple_simple` is stated the same way. The statement text is
  unchanged.

## Context opens (not a statement change)

The file has `open CategoryTheory MonoidalCategory Module`, so that `𝟙_`, `⊗` and `ᘁ`,
`Simple`, `≅`, and `finrank` resolve as written.

## Wiring edit (Lean Green, 2026-11-10)

- Before: `gauge_no_dangling` and `gauge_pair_finrank` were declared after `end GaugeSupport`, at top level.
- After: both are inside `namespace GaugeSupport` (full names `GaugeSupport.gauge_no_dangling`, `GaugeSupport.gauge_pair_finrank`). Statement text unchanged.
- Reason: `scripts/verify.py` requires one namespace per file and audits theorems as `<namespace>.<name>`; the axiom audit could not find the top-level names.

## DualSimple.lean (Green, 2026-11-10)

- New file `DualSimple.lean` (namespace `GaugeSupport`) proves
  `dual_simple (V : FDRep k G) [Simple V] : Simple Vᘁ` for any field `k` and group `G`,
  with no extra hypotheses, plus the global instance `instSimpleDual`.
- `lattice_support_rule_of_simple` restates `lattice_support_rule` with `[hd : ∀ e, Simple (π e)ᘁ]`
  removed and proves it from `dual_simple`. So the dual-simplicity hypothesis is discharged.
  The original `lattice_support_rule` statement is unchanged.
- The file is in `complete_files`, so the gate freezes all 12 of its theorems, the helper lemmas
  included, not just the two headline ones. Red OK'd that.
- False control: `FalseControls/DualSimpleControl.lean` (`∀ V : FDRep ℚ Unit, Simple Vᘁ`,
  false for the zero representation) is rejected.
- Gate: 493 theorems, 4 false controls rejected, 415 frozen, axioms propext / Classical.choice / Quot.sound.

## GaugeSupportRegroup.lean (Grey, 2026-11-11)

- New file `GaugeSupportRegroup.lean` (namespace `GaugeSupport`): the regrouping by vertex.
  The vertex-regrouped block is Mathlib's `PiTensorProduct` `⨂_v W_v(π)` with
  `W_v(π) = vertexRep (incident Γ π v)`, and the gauge group `Vx → G` acts factor by factor
  (`gaugeAction`, built from `PiTensorProduct.mapMonoidHom`).
- Proved with no extra hypotheses (any group, any field; no complete reducibility):
  `gauge_invariant_eq_zero_of_vertex` / `vertex_invariant_ne_bot_of_gauge_invariant`
  (a nonzero gauge-invariant vector of `⨂_v W_v` forces a nonzero invariant in every `W_v`),
  and the converse direction for pure tensors `tprod_gauge_invariant`.
- Named assumption `PeterWeylLattice` (abbreviation `PeterWeylSU3` for `ℂ`, `SU(3)`), a
  structure, not an axiom: gauge-equivariant block projections `proj π : H → ⨂_v W_v(π)` that
  separate points. It packages Peter–Weyl link by link and the reshuffle
  `⊗_e (V_{π e} ⊗ V_{π e}*) ≅ ⊗_v W_v(π)`; neither is proved here. `PeterWeylLattice.model`
  shows the structure is inhabited (block-sum model), so the assumption is not vacuous.
- `support_vertex_invariant` discharges the `hinv` hypothesis of
  `lattice_support_rule_of_simple` for every labelling in the support of a gauge-invariant
  state; `gauge_support_rule_regrouped` and `gauge_support_rule_regrouped_SU3` state the
  resulting rule. Frozen statements of earlier files are unchanged.
- The file is in `complete_files` (all 12 theorems frozen).
- False controls: `RegroupControl` (drop the vanishing-vertex hypothesis; the open goal
  `invariants 1 = ⊥` is false), `SupportControl` (labelling outside the support), and
  `RegroupedRuleControl` (SU(3) rule without gauge invariance). All rejected (unsolved goals).

## GaugeSupportReshuffle.lean (Grey, 2026-11-11)

- New file `GaugeSupportReshuffle.lean` (namespace `GaugeSupport`): the edge-to-vertex
  reshuffle `⊗_e (V_{π e} ⊗ V_{π e}*) ≅ ⊗_v W_v(π)`, taken out of the `PeterWeylLattice`
  assumption and proved.
- Orientation, read off `incident` / `vertexRep`: the source end of a link carries `π e`, the
  target end `(π e)ᘁ`; `W_v` is the right-nested tensor of the factors at `v`, outgoing links
  first, then incoming, each in `Finset.toList` order, ending in `𝟙`.
- `reshuffle : EdgeBlock π ≃ₗ[k] RegroupedBlock Γ π` is the composite of `pairEquiv`
  (pair the two ends of each link), `regroupEquiv` (regroup half-edges by vertex) and
  `vertexEquiv` (list-tensor at each vertex, `listEquiv`, then `eqToIso` onto `vertexRep`).
  `reshuffle_tprod` gives its value on pure tensors (the factor permutation);
  `reshuffle_equivariant` / `reshuffle_symm_equivariant` show it intertwines `edgeGauge` (copy
  at `src e` on `V`, copy at `tgt e` on `V*`) with `blockGauge`. Any group, any field.
- New named assumption `PeterWeylLinks` / `PeterWeylLinksSU3` (a structure, not an axiom):
  Peter–Weyl link by link onto `⊗_e (V ⊗ V*)` only. `PeterWeylLinks.toLattice` builds
  `PeterWeylLattice` from it; `gauge_support_rule_links` and `_SU3` restate the regrouped rule
  under the weaker assumption; `PeterWeylLinks.model` shows it is inhabited.
- Frozen statements of earlier files are unchanged; the file is in `complete_files`
  (all 34 theorems frozen, 521 frozen in total).
- False control: `ReshuffleDropControl` (drop the `V*` end of a single link: claims
  `⊗_e (V ⊗ V*) ≃ ⊗_e V` for `V = ℚ²`; dimensions 4 vs 2; rejected, unsolved goal `False`).
- Gate: 599 theorems, 14 false controls.

## GaugeSupportReshuffleRep.lean (Grey, 2026-11-11)

- New file `GaugeSupportReshuffleRep.lean` (namespace `GaugeSupport`): `reshuffle` packaged as
  one Mathlib `Representation.Equiv` for the gauge group `Vx → G`.
- `edgeGaugeRep` / `blockGaugeRep` are abbreviations of the existing representations
  `edgeGauge` / `blockGauge` (both already monoid homs), so application is definitional.
- `reshuffleRepEquiv : (edgeGaugeRep Γ π).Equiv (blockGaugeRep Γ π)`, built with
  `Representation.Equiv.mk` from `reshuffle` and `reshuffle_equivariant`;
  `reshuffleRepEquiv_toLinearEquiv` (rfl) says its linear equivalence is `reshuffle`.
- `repEquiv_map_invariants` (any `Representation.Equiv`), `reshuffle_map_invariants` and
  `reshuffleInvariantsEquiv` (via `LinearEquiv.ofSubmodules`): the reshuffle maps the link
  invariants onto the vertex invariants. `mem_blockGaugeRep_invariants_iff` identifies the
  latter with `IsGaugeInvariant`.
- `toLattice_proj_eq` restates `PeterWeylLinks.toLattice` through the iso;
  `PeterWeylLinks.proj_mem_invariants` and `toLattice_proj_mem_invariants` match the
  components of a gauge-invariant state on both sides.
- Frozen statements of earlier files are unchanged; the file is in `complete_files`
  (all 12 theorems frozen, 533 frozen in total).
- False control: `ReshuffleRepControl` (the iso against the link action with `src`/`tgt`
  swapped on one link `0 → 1`, `ℚˣ` acting on `ℚ` by scalars: the action on `V ⊗ V*` is
  `g 0 / g 1`, the swapped one `g 1 / g 0`; rejected, unsolved goals).
- Gate: 611 theorems, 15 false controls.
