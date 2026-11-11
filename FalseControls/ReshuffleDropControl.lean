import GaugeSupportReshuffle
open CategoryTheory MonoidalCategory Module TensorProduct GaugeSupport

/-- `ℚ²` with the trivial action of the trivial group. -/
noncomputable abbrev V2 : FDRep ℚ Unit := FDRep.of (Representation.trivial ℚ Unit (Fin 2 → ℚ))

-- False: a "reshuffle" that drops the `V*` end of the single link `e`. The link block
-- `⊗_e (V ⊗ V*)` has dimension 2 · 2 = 4 but `⊗_e V` has dimension 2, so no linear
-- isomorphism (equivariant or not) exists. Comparing dimensions with the proved
-- `finrank_piTensorProduct` leaves the false goal `2 * 2 = 2`, which `norm_num` refutes.
example : Nonempty (EdgeBlock (fun _ : Fin 1 => V2) ≃ₗ[ℚ] ⨂[ℚ] _ : Fin 1, (V2 : Type)) := by
  refine ⟨LinearEquiv.ofFinrankEq _ _ ?_⟩
  have hV : finrank ℚ V2 = 2 := Module.finrank_fin_fun ℚ
  have hD : finrank ℚ ((V2ᘁ : FDRep ℚ Unit) : Type) = 2 :=
    (Subspace.dual_finrank_eq (K := ℚ) (V := V2)).trans hV
  simp only [finrank_piTensorProduct, Fin.prod_univ_one, Module.finrank_tensorProduct, hV, hD]
  norm_num
