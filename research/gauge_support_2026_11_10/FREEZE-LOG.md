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
