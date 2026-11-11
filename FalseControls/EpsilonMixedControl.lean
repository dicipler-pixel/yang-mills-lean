import SingletWitnessSU3

/- False control: claims that `ε = ∑ ε_{ijk} eᵢ ⊗ eⱼ ⊗ e_k*`, the Levi-Civita tensor with the
   third factor moved to `3̄`, is SU(3)-invariant in `3 ⊗ 3 ⊗ 3̄`. The proof attempt is the
   route that proves `epsVec3_invariant`: every factor would have to move by the same
   determinant-one matrix `g`. The `3̄` factor moves by `(g⁻¹)ᵀ` instead, so Lean rejects it.
   The claim is false: the centre element `ω·I` scales this vector by `ω·ω·ω² = ω ≠ 1`
   (`epsMixed_centre`, `epsMixed_not_invariant`, `invariants_mixed_eq_bot`). Must fail to
   compile. -/
namespace SingletWitnessSU3

open CategoryTheory MonoidalCategory CentreCharacterSU3

theorem epsMixed_invariant (g : SU3) :
    (fund ⊗ (fund ⊗ antifund)).ρ g epsMixed = epsMixed := by
  have hc : ∀ a b c, ∑ i, ∑ j, ∑ k, eps i j k * (g.1 a i * (g.1 b j * g.1 c k)) = eps a b c :=
    fun a b c => by rw [eps_contract, det_eq_one, one_mul]
  exact eps_raw (fund.ρ g) ((fund ⊗ antifund).ρ g) frameFund.u mixedT (fun a i => g.1 a i)
    (frameFund.moves g)
    (fun j k => tmul_raw (fund.ρ g) (antifund.ρ g) frameFund.u frameAntifund.u
      (fun a i => g.1 a i) (frameFund.moves g) (frameAntifund.moves g) j k) hc

end SingletWitnessSU3
