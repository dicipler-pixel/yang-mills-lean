import SymWitnessSU3

/- False control: claims that `6 ⊗ 3 = V(2, 0) ⊗ fund` has a nonzero SU(3)-invariant. Triality
   allows it (`2 + 1 ≡ 0 mod 3`): `ω·I` acts on `3 ⊗ 6` by `ω · ω² = 1` (`centreActs_fund_sym`),
   so the centre gives no contradiction. The proof attempt assumes the invariants vanish, records
   that the centre acts trivially, and is left with the goal `False`; Lean rejects it with
   unsolved goals. The claim is false: `invariants_sym_fund_eq_bot` (the sign matrices, the
   3-4-5 rotation and the cyclic permutation force every invariant of `3 ⊗ Sym²(3)` to vanish;
   classically `3 ⊗ 6 = 8 ⊕ 10`). Must fail to compile. -/
namespace SymWitnessSU3

open CategoryTheory MonoidalCategory CentreCharacterSU3 IrrepEmbedSU3 TrialityVertex

theorem sym_fund_invariant :
    Representation.invariants (irrepRep 2 0 ⊗ fund).ρ ≠ ⊥ := by
  intro h
  have hc : CentreActs zω 1 (fund ⊗ irrepRep 2 0) := centreActs_fund_sym
  have hb : Representation.invariants (irrepRep 2 0 ⊗ fund).ρ = ⊥ := h

end SymWitnessSU3
