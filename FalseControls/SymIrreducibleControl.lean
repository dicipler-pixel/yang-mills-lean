-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026 Jeromie Beasley. See LICENSING.md.
import SymIrreducibleSU3

/- False control: claims the exact negation of the irreducibility of `V(2, 0) = Sym²(3)`, i.e.
   that `V(2, 0)` has some nonzero proper SU(3)-stable subspace. The proof attempt takes the
   natural candidate, the highest-weight line `ℂ · (e₁ ⊗ e₁ ⊗ 1)` (stable under the diagonal
   torus), proves it nonzero and proper (dimension 1 < 6), records the proved dichotomy
   `irrep20_invariant_eq_bot_or_top`, and is left with the stability goal
   `(irrepRep 2 0).ρ g w ∈ span {hwIrrep 2 0}`; Lean rejects it with unsolved goals. The claim
   is false: the cyclic permutation moves `E₀₀` to `E₁₁` off the line, and in general
   `irrep20_invariant_eq_bot_or_top` / `simple_irrep20` (sign matrices, the 3-4-5 rotation,
   `τ = diag(i, 1, -i)` and the cyclic permutation) show every nonzero stable subspace is `⊤`.
   Must fail to compile. -/
namespace SymIrreducibleSU3

open CentreCharacterSU3 IrrepEmbedSU3 SymWitnessSU3

theorem irrep20_has_proper_invariant :
    ∃ W : Submodule ℂ (irrepRep 2 0),
      (∀ g, ∀ w ∈ W, (irrepRep 2 0).ρ g w ∈ W) ∧ W ≠ ⊥ ∧ W ≠ ⊤ := by
  have hdich := irrep20_invariant_eq_bot_or_top
  refine ⟨Submodule.span ℂ {hwIrrep 2 0}, fun g w hw => ?_, ?_, ?_⟩
  · skip
  · rw [Ne, Submodule.span_singleton_eq_bot]
    exact hwIrrep_ne_zero 2 0
  · intro htop
    have h1 := finrank_span_singleton (K := ℂ) (hwIrrep_ne_zero 2 0)
    rw [htop, finrank_top, finrank_irrepRep20] at h1
    norm_num at h1

end SymIrreducibleSU3
