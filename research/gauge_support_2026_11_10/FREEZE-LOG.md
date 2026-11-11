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
