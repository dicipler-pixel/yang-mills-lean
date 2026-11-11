/-
GaugeSupportFDRep.lean — the two frozen targets of the SU(3) gauge support rule, stated in
Mathlib's `FDRep` (finite-dimensional representations of a group over a field).

* `gauge_no_dangling` (T1): a simple representation not isomorphic to the unit `𝟙` has no
  nonzero invariant vector. Any group, any field.
* `gauge_pair_finrank` (T2): over an algebraically closed field, for simple `V W`,
  `dim (Vᘁ ⊗ W)^G = 1` if `V ≅ W` and `0` otherwise.

Route: invariants of `X` ≃ₗ `𝟙 ⟶ X`; braiding `Vᘁ ⊗ W ≅ W ⊗ Vᘁ`; the rigid adjunction
`(𝟙 ⊗ V ⟶ W) ≃ₗ (𝟙 ⟶ W ⊗ Vᘁ)`; left unitor; `FDRep.finrank_hom_simple_simple`.
Statement syntax fixes are recorded in `research/gauge_support_2026_11_10/FREEZE-LOG.md`.
No `sorry`, no `native_decide`, no new axioms. Checked on Lean v4.33.0 / Mathlib v4.33.0.
-/
import Mathlib.RepresentationTheory.FDRep
import Mathlib.RepresentationTheory.Invariants
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided

open CategoryTheory MonoidalCategory Module

namespace GaugeSupport

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G]

/-- A `G`-invariant vector `v` gives the morphism `𝟙 ⟶ X`, `c ↦ c • v`. -/
noncomputable def unitHom (X : FDRep k G) (v : Representation.invariants X.ρ) :
    𝟙_ (FDRep k G) ⟶ X :=
  ⟨InducedCategory.homMk (ModuleCat.ofHom (LinearMap.toSpanSingleton k X v.1)), fun g => by
    ext
    have := v.2 g
    simp_all⟩

example (X : FDRep k G) (v : Representation.invariants X.ρ) (c : k) :
    (unitHom X v).hom.hom.hom c = c • v.1 := rfl

theorem unit_ρ_apply (g : G) (x : k) : (𝟙_ (FDRep k G)).ρ g x = x := rfl

/-- Linear-algebra half: invariant vectors ↔ invariant linear maps `k → X`. -/
noncomputable def invariantsEquivLinHomInvariants (X : FDRep k G) :
    Representation.invariants X.ρ ≃ₗ[k]
      Representation.invariants (Representation.linHom (𝟙_ (FDRep k G)).ρ X.ρ) where
  toFun v := ⟨LinearMap.toSpanSingleton k X v.1, fun g => by
    ext
    simp only [Representation.linHom_apply, LinearMap.comp_apply]
    show X.ρ g ((1 : k) • v.1) = (1 : k) • v.1
    rw [one_smul]
    exact v.2 g⟩
  map_add' v w := by ext; simp
  map_smul' c v := by ext; simp
  invFun f := ⟨f.1 (1 : k), fun g => by
    have h := LinearMap.congr_fun (f.2 g) (1 : k)
    simpa only [Representation.linHom_apply, LinearMap.comp_apply, unit_ρ_apply] using h⟩
  left_inv v := by
    ext
    show (1 : k) • v.1 = v.1
    exact one_smul k v.1
  right_inv f := by
    ext
    simp

/-- The invariants of `X` are the morphisms `𝟙 ⟶ X`. -/
noncomputable def invariantsEquivUnitHom (X : FDRep k G) :
    Representation.invariants X.ρ ≃ₗ[k] (𝟙_ (FDRep k G) ⟶ X) :=
  invariantsEquivLinHomInvariants X ≪≫ₗ
    Representation.linHom.invariantsEquivFDRepHom (𝟙_ (FDRep k G)) X

theorem unitHom_apply (X : FDRep k G) (v : Representation.invariants X.ρ) (c : k) :
    (unitHom X v).hom.hom.hom c = c • v.1 := rfl

/-- `tensorRightHomEquiv` is `k`-linear in `FDRep k G`. -/
noncomputable def tensorRightHomLinearEquiv (X Y Y' Z : FDRep k G) [ExactPairing Y Y'] :
    (X ⊗ Y ⟶ Z) ≃ₗ[k] (X ⟶ Z ⊗ Y') :=
  { tensorRightHomEquiv X Y Y' Z with
    map_add' := fun f g => by simp [tensorRightHomEquiv]
    map_smul' := fun c f => by simp [tensorRightHomEquiv] }

/-- **T1 (frozen; see FREEZE-LOG for the one syntax fix).** -/
theorem gauge_no_dangling {k G} [Field k] [Group G] (V : FDRep k G) [Simple V]
    (h : IsEmpty (𝟙_ (FDRep k G) ≅ V)) : Representation.invariants V.ρ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  by_contra hv0
  let f := unitHom V ⟨v, hv⟩
  have hinj : Function.Injective f.hom.hom.hom := fun a b hab => by
    rw [unitHom_apply, unitHom_apply] at hab
    exact smul_left_injective k hv0 hab
  have hmono' : Mono ((Action.forget (FGModuleCat k) G ⋙
      forget₂ (FGModuleCat k) (ModuleCat k)).map f) :=
    (ModuleCat.mono_iff_injective _).2 hinj
  have hmono : Mono f := Functor.mono_of_mono_map _ hmono'
  have hne : f ≠ 0 := by
    intro hf0
    have h1 := congrArg (fun φ : 𝟙_ (FDRep k G) ⟶ V => φ.hom.hom.hom (1 : k)) hf0
    simp only [f, unitHom_apply, one_smul] at h1
    exact hv0 (h1.trans (by simp))
  have : IsIso f := isIso_of_mono_of_nonzero hne
  exact h.false (asIso f)

open scoped Classical in
/-- **T2 (frozen; see FREEZE-LOG for the syntax fixes).** -/
theorem gauge_pair_finrank {k G} [Field k] [IsAlgClosed k] [Group G]
    (V W : FDRep k G) [Simple V] [Simple W] :
    finrank k (Representation.invariants (Vᘁ ⊗ W).ρ) = if Nonempty (V ≅ W) then 1 else 0 := by
  rw [(invariantsEquivUnitHom (Vᘁ ⊗ W)).finrank_eq,
    (Linear.homCongr k (Iso.refl _) (β_ Vᘁ W)).finrank_eq,
    (tensorRightHomLinearEquiv (𝟙_ (FDRep k G)) V Vᘁ W).symm.finrank_eq,
    (Linear.homCongr k (λ_ V) (Iso.refl W)).finrank_eq]
  exact FDRep.finrank_hom_simple_simple V W

#print axioms gauge_no_dangling
#print axioms gauge_pair_finrank

end GaugeSupport
