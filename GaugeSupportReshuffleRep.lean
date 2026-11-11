/-
GaugeSupportReshuffleRep.lean — the reshuffle as one representation isomorphism
(Grey, 2026-11-11).

`GaugeSupportReshuffle.lean` proves `reshuffle : EdgeBlock π ≃ₗ[k] RegroupedBlock Γ π`
(`⊗_e (V_{π e} ⊗ V_{π e}*) ≅ ⊗_v W_v`) and its equivariance one gauge element at a time. Here
it is packaged as a single object of Mathlib's `Representation.Equiv` (a bijective
intertwining map, `Mathlib.RepresentationTheory.Intertwining`) for the gauge group `Vx → G`:
* `edgeGaugeRep` / `blockGaugeRep`: the link action `edgeGauge` and the vertex action
  `blockGauge`, which are already `Representation k (Vx → G) _` (monoid homs); the new names
  are abbreviations, so their application is definitionally `edgeGauge` / `blockGauge`.
* `reshuffleRepEquiv : (edgeGaugeRep Γ π).Equiv (blockGaugeRep Γ π)`, with
  `reshuffleRepEquiv_toLinearEquiv : (reshuffleRepEquiv Γ π).toLinearEquiv = reshuffle Γ π`.
* `repEquiv_map_invariants` (any `Representation.Equiv`) and `reshuffle_map_invariants`:
  the reshuffle maps the invariants of the link action onto the invariants of the vertex
  action; `reshuffleInvariantsEquiv` is the resulting linear equivalence of invariant
  submodules.
* `toLattice_proj_eq`: `PeterWeylLinks.toLattice` is projection followed by the iso.
* `PeterWeylLinks.proj_mem_invariants` / `toLattice_proj_mem_invariants`: the components of a
  gauge-invariant state are invariants on both sides, matched by `reshuffleInvariantsEquiv`.
No `sorry`, no `native_decide`, no new axioms. Peter–Weyl for `L²(SU(3))` is still the named
assumption `PeterWeylLinks`. Checked on Lean v4.33.0 / Mathlib v4.33.0.
-/
import GaugeSupportReshuffle
import Mathlib.RepresentationTheory.Intertwining

open CategoryTheory MonoidalCategory Module TensorProduct

namespace GaugeSupport

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G]

/-! ### Any equivalence of representations matches invariants -/

section General

variable {H₁ H₂ : Type*} [AddCommGroup H₁] [Module k H₁] [AddCommGroup H₂] [Module k H₂]
  {Γg : Type*} [Group Γg] {ρ : Representation k Γg H₁} {σ : Representation k Γg H₂}

/-- An equivalence of representations maps the invariants of `ρ` onto those of `σ`. -/
theorem repEquiv_map_invariants (φ : ρ.Equiv σ) :
    (Representation.invariants ρ).map φ.toLinearEquiv.toLinearMap =
      Representation.invariants σ := by
  have hφ : ∀ g x, φ.toLinearEquiv (ρ g x) = σ g (φ.toLinearEquiv x) :=
    fun g x => LinearMap.congr_fun (φ.isIntertwining' g) x
  ext y
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩ g
    show σ g (φ.toLinearEquiv x) = φ.toLinearEquiv x
    rw [← hφ, hx g]
  · intro hy
    refine ⟨φ.toLinearEquiv.symm y, fun g => ?_, φ.toLinearEquiv.apply_symm_apply y⟩
    apply φ.toLinearEquiv.injective
    rw [hφ, LinearEquiv.apply_symm_apply]
    exact hy g

/-- The linear equivalence of invariant submodules induced by an equivalence of
representations. -/
noncomputable def repEquivInvariants (φ : ρ.Equiv σ) :
    Representation.invariants ρ ≃ₗ[k] Representation.invariants σ :=
  φ.toLinearEquiv.ofSubmodules _ _ (repEquiv_map_invariants φ)

theorem repEquivInvariants_apply (φ : ρ.Equiv σ) (x : Representation.invariants ρ) :
    (repEquivInvariants φ x : H₂) = φ.toLinearEquiv x := rfl

end General

/-! ### The reshuffle as a `Representation.Equiv` -/

section Rep

variable {Vx E : Type*} [Fintype E] (Γ : OrientedGraph Vx E) (π : E → FDRep k G)

/-- The link action as a representation of `Vx → G` (copy at `src e` on `V_{π e}`, copy at
`tgt e` on `V_{π e}*`). -/
noncomputable abbrev edgeGaugeRep : Representation k (Vx → G) (EdgeBlock π) := edgeGauge Γ π

/-- The vertex action as a representation of `Vx → G` (copy at `v` on `W_v`). -/
noncomputable abbrev blockGaugeRep : Representation k (Vx → G) (RegroupedBlock Γ π) :=
  blockGauge Γ π

omit [Fintype E] in
theorem edgeGaugeRep_apply (g : Vx → G) :
    edgeGaugeRep Γ π g = PiTensorProduct.map fun e =>
      TensorProduct.map ((π e).ρ (g (Γ.src e))) ((π e)ᘁ.ρ (g (Γ.tgt e))) := rfl

theorem blockGaugeRep_apply (g : Vx → G) :
    blockGaugeRep Γ π g = PiTensorProduct.map fun v => (vertexRep (incident Γ π v)).ρ (g v) := rfl

variable [Fintype Vx] [DecidableEq Vx]

/-- **The reshuffle as one isomorphism of representations of `Vx → G`**:
`⊗_e (V_{π e} ⊗ V_{π e}*) ≅ ⊗_v W_v`, intertwining `edgeGaugeRep` and `blockGaugeRep`. -/
noncomputable def reshuffleRepEquiv : (edgeGaugeRep Γ π).Equiv (blockGaugeRep Γ π) :=
  Representation.Equiv.mk (reshuffle Γ π)
    (fun g => LinearMap.ext fun t => reshuffle_equivariant Γ π g t)

/-- Its underlying linear equivalence is `reshuffle`. -/
theorem reshuffleRepEquiv_toLinearEquiv :
    (reshuffleRepEquiv Γ π).toLinearEquiv = reshuffle Γ π := rfl

theorem reshuffleRepEquiv_apply (t : EdgeBlock π) :
    reshuffleRepEquiv Γ π t = reshuffle Γ π t := rfl

/-- **Invariants correspond**: the reshuffle maps the gauge invariants of the link block onto
the gauge invariants of the vertex-regrouped block. -/
theorem reshuffle_map_invariants :
    (Representation.invariants (edgeGaugeRep Γ π)).map (reshuffle Γ π).toLinearMap =
      Representation.invariants (blockGaugeRep Γ π) :=
  repEquiv_map_invariants (reshuffleRepEquiv Γ π)

/-- The linear equivalence `(⊗_e (V ⊗ V*))^{G^V} ≃ (⊗_v W_v)^{G^V}` given by the reshuffle. -/
noncomputable def reshuffleInvariantsEquiv :
    Representation.invariants (edgeGaugeRep Γ π) ≃ₗ[k]
      Representation.invariants (blockGaugeRep Γ π) :=
  repEquivInvariants (reshuffleRepEquiv Γ π)

theorem reshuffleInvariantsEquiv_apply (x : Representation.invariants (edgeGaugeRep Γ π)) :
    (reshuffleInvariantsEquiv Γ π x : RegroupedBlock Γ π) = reshuffle Γ π x := rfl

omit [Fintype Vx] [DecidableEq Vx] in
/-- Membership in the vertex-side invariants is `IsGaugeInvariant` of `GaugeSupportRegroup`. -/
theorem mem_blockGaugeRep_invariants_iff (t : RegroupedBlock Γ π) :
    t ∈ Representation.invariants (blockGaugeRep Γ π) ↔
      IsGaugeInvariant (VertexSpace Γ π) (fun v => (vertexRep (incident Γ π v)).ρ) t :=
  Representation.mem_invariants _ t

end Rep

/-! ### `PeterWeylLinks.toLattice` through the iso -/

section Links

variable {Vx E : Type*} [Fintype E] [Fintype Vx] [DecidableEq Vx]
  {Γ : OrientedGraph Vx E} {Irr : Type*} {irr : Irr → FDRep k G}
  {H : Type*} [AddCommGroup H] [Module k H] {gauge : Representation k (Vx → G) H}

/-- The block projections of `PeterWeylLinks.toLattice` are the link projections followed by
the representation isomorphism `reshuffleRepEquiv`. -/
theorem toLattice_proj_eq (PW : PeterWeylLinks k G Γ Irr irr H gauge) (π : E → Irr) :
    PW.toLattice.proj π = (reshuffleRepEquiv Γ (irr ∘ π)).toLinearMap ∘ₗ PW.proj π := rfl

omit [Fintype E] [Fintype Vx] [DecidableEq Vx] in
/-- The link component of a gauge-invariant state is an invariant of the link action. -/
theorem PeterWeylLinks.proj_mem_invariants (PW : PeterWeylLinks k G Γ Irr irr H gauge) (ψ : H)
    (hψ : ∀ g, gauge g ψ = ψ) (π : E → Irr) :
    PW.proj π ψ ∈ Representation.invariants (edgeGaugeRep Γ (irr ∘ π)) := by
  intro g
  rw [← PW.proj_equivariant, hψ g]

/-- Its image under the iso is the vertex-side component, an invariant of the vertex action. -/
theorem toLattice_proj_mem_invariants (PW : PeterWeylLinks k G Γ Irr irr H gauge) (ψ : H)
    (hψ : ∀ g, gauge g ψ = ψ) (π : E → Irr) :
    PW.toLattice.proj π ψ ∈ Representation.invariants (blockGaugeRep Γ (irr ∘ π)) ∧
      (reshuffleInvariantsEquiv Γ (irr ∘ π) ⟨PW.proj π ψ, PW.proj_mem_invariants ψ hψ π⟩ :
        RegroupedBlock Γ (irr ∘ π)) = PW.toLattice.proj π ψ := by
  refine ⟨?_, rfl⟩
  rw [← reshuffle_map_invariants]
  exact ⟨PW.proj π ψ, PW.proj_mem_invariants ψ hψ π, rfl⟩

end Links

end GaugeSupport

#print axioms GaugeSupport.repEquiv_map_invariants
#print axioms GaugeSupport.reshuffleRepEquiv
#print axioms GaugeSupport.reshuffleRepEquiv_toLinearEquiv
#print axioms GaugeSupport.reshuffle_map_invariants
#print axioms GaugeSupport.reshuffleInvariantsEquiv
#print axioms GaugeSupport.toLattice_proj_eq
#print axioms GaugeSupport.toLattice_proj_mem_invariants
