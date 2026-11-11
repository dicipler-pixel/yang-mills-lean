import GaugeSupportReshuffleRep
open CategoryTheory MonoidalCategory Module TensorProduct GaugeSupport

/-- `ℚ` with `ℚˣ` acting by scalar multiplication (a faithful character). -/
noncomputable abbrev Lq : FDRep ℚ ℚˣ :=
  FDRep.of ((Algebra.lsmul ℚ ℚ ℚ).toMonoidHom.comp (Units.coeHom ℚ))

/-- One link `() : 0 → 1`. -/
def oneLink : OrientedGraph (Fin 2) Unit := ⟨fun _ => 0, fun _ => 1⟩

/-- The link action with source and target swapped: the copy at `tgt` acts on `V`, the copy at
`src` on `V*` (the wrong orientation). -/
noncomputable def swappedGauge (g : Fin 2 → ℚˣ) : EdgeBlock (fun _ : Unit => Lq) →ₗ[ℚ]
    EdgeBlock (fun _ : Unit => Lq) :=
  PiTensorProduct.map fun e => TensorProduct.map (Lq.ρ (g (oneLink.tgt e)))
    ((Lqᘁ : FDRep ℚ ℚˣ).ρ (g (oneLink.src e)))

-- False: the reshuffle iso does not intertwine the swapped link action with the vertex action.
-- On `V ⊗ V*` the correct action of `g` is the scalar `g 0 / g 1`, the swapped one `g 1 / g 0`;
-- at `g = (2, 1)` they are `2` and `1/2`. Using `reshuffle_equivariant` reduces the claim to
-- `reshuffle (swappedGauge g t) = reshuffle (edgeGauge g t)`, which stays open (it is false).
example : ∀ (g : Fin 2 → ℚˣ) (t : EdgeBlock (fun _ : Unit => Lq)),
    reshuffleRepEquiv oneLink (fun _ => Lq) (swappedGauge g t) =
      blockGaugeRep oneLink (fun _ => Lq) g (reshuffleRepEquiv oneLink (fun _ => Lq) t) := by
  intro g t
  rw [reshuffleRepEquiv_apply, reshuffleRepEquiv_apply, blockGaugeRep, ← reshuffle_equivariant]
