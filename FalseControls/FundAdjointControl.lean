import AdjointWitnessSU3

/- False control: claims that `3 ⊗ 8 = fund ⊗ V(1, 1)` has a nonzero SU(3)-invariant, as
   `3 ⊗ 3̄ ⊗ 8` does (`ξᵀXη`). The proof attempt assumes the invariants vanish and looks for a
   contradiction through the centre: `ω·I` acts on `3 ⊗ 8` by `ω · 1 = ω`
   (`centreActs_fund_adjoint`). That gives none, since vanishing invariants are exactly what the
   centre forces, so the attempt is left with the goal `False` and Lean rejects it with unsolved
   goals. The claim is false: `invariants_fund_adjoint_eq_bot` (a nonzero invariant would force
   `ω = 1`; triality `1 + 0 ≢ 0 mod 3`). Must fail to compile. -/
namespace AdjointWitnessSU3

open CategoryTheory MonoidalCategory CentreCharacterSU3 IrrepEmbedSU3 TrialityVertex

theorem fund_adjoint_invariant :
    Representation.invariants (fund ⊗ irrepRep 1 1).ρ ≠ ⊥ := by
  intro h
  have hc : CentreActs zω ω (fund ⊗ irrepRep 1 1) := centreActs_fund_adjoint
  have hb : Representation.invariants (fund ⊗ irrepRep 1 1).ρ = ⊥ := h

end AdjointWitnessSU3
