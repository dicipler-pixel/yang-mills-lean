/-
DualSimple.lean — the dual of a simple finite-dimensional representation is simple
(Green, 2026-11-10).

Discharges the hypothesis `[hd : ∀ e, Simple (π e)ᘁ]` of `lattice_support_rule` (and the
`[Simple x.repᘁ]` arguments of `vertex_two_valent`) in `GaugeSupportLattice.lean`.
Any group `G`, any field `k`; no algebraic closure, no characteristic assumption.

Route (linear algebra inside `FDRep`):
* `dual_ρ_apply`: the action on `Vᘁ` is `(g • φ) x = φ (g⁻¹ • x)`. Mathlib gives
  `Vᘁ.ρ g = (V.ρ g⁻¹)ᘁ` (`Action.rightDual_ρ`); the rigid mate in `FGModuleCat` is the
  transpose, read off `rightAdjointMate_comp_evaluation` on a pure tensor.
* `subIncl`: a `G`-stable subspace gives a mono into `V`; Schur
  (`isIso_of_mono_of_nonzero`) then shows a simple `V` has no stable subspace except `⊥, ⊤`.
* `injective_of_mono`: a mono in `FDRep` is injective (its kernel is a stable subspace
  whose inclusion is killed by the mono).
* For a nonzero mono `f : Y ⟶ Vᘁ`, the range `U ⊆ V*` is stable, so its annihilator
  `U.dualCoannihilator ⊆ V` is stable, hence `⊥` or `⊤`. `⊤` forces `f = 0`; `⊥` forces
  `U = ⊤` (`Subspace.dualCoannihilator_dualAnnihilator_eq`, finite dimension), so `f` is
  bijective and an isomorphism.
No `sorry`, no `native_decide`, no new axioms. Checked on Lean v4.33.0 / Mathlib v4.33.0.
-/
import GaugeSupportLattice

open CategoryTheory MonoidalCategory Module

namespace GaugeSupport

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G]

theorem fgModuleCat_rightAdjointMate_apply {X Y : FGModuleCat.{u} k} (f : X ⟶ Y)
    (φ : Module.Dual k Y) (x : X) :
    (show Module.Dual k X from (fᘁ).hom.hom φ) x = φ (f.hom.hom x) := by
  have := congrArg (fun m => m.hom.hom (φ ⊗ₜ x)) (rightAdjointMate_comp_evaluation f)
  simp at this
  exact this

theorem dual_ρ_apply (V : FDRep.{u} k G) (g : G) (φ : Module.Dual k V) (x : V) :
    (show Module.Dual k V from (Vᘁ).ρ g φ) x = φ (V.ρ g⁻¹ x) := by
  show (show Module.Dual k V from (Action.ρ Vᘁ g).hom.hom φ) x = φ ((Action.ρ V g⁻¹).hom.hom x)
  rw [Action.rightDual_ρ]
  exact fgModuleCat_rightAdjointMate_apply _ φ x

noncomputable def subIncl (X : FDRep.{u} k G) (W : Submodule k X)
    (hW : ∀ g, ∀ w ∈ W, X.ρ g w ∈ W) :
    FDRep.of (Subrepresentation.toRepresentation
      (⟨W, fun g _ hw => hW g _ hw⟩ : Subrepresentation X.ρ)) ⟶ X :=
  ⟨InducedCategory.homMk (ModuleCat.ofHom W.subtype), fun g => by ext; rfl⟩

theorem subIncl_apply (X : FDRep.{u} k G) (W : Submodule k X)
    (hW : ∀ g, ∀ w ∈ W, X.ρ g w ∈ W) (w) : (subIncl X W hW).hom.hom.hom w = w.1 := rfl

theorem bijective_of_isIso {X Y : FDRep.{u} k G} (f : X ⟶ Y) [IsIso f] :
    Function.Bijective f.hom.hom.hom :=
  ConcreteCategory.bijective_of_isIso
    ((Action.forget (FGModuleCat k) G ⋙ forget₂ (FGModuleCat k) (ModuleCat k)).map f)

theorem isIso_of_bijective {X Y : FDRep.{u} k G} (f : X ⟶ Y)
    (hf : Function.Bijective f.hom.hom.hom) : IsIso f := by
  let e := (LinearEquiv.ofBijective f.hom.hom.hom hf).toFGModuleCatIso
  have : f.hom = e.hom := by ext; rfl
  have : IsIso f.hom := by rw [this]; infer_instance
  exact Action.isIso_of_hom_isIso f

theorem mono_subIncl (X : FDRep.{u} k G) (W : Submodule k X)
    (hW : ∀ g, ∀ w ∈ W, X.ρ g w ∈ W) : Mono (subIncl X W hW) := by
  have hmono' : Mono ((Action.forget (FGModuleCat k) G ⋙
      forget₂ (FGModuleCat k) (ModuleCat k)).map (subIncl X W hW)) :=
    (ModuleCat.mono_iff_injective _).2 W.injective_subtype
  exact Functor.mono_of_mono_map _ hmono'

theorem subIncl_ne_zero (X : FDRep.{u} k G) (W : Submodule k X)
    (hW : ∀ g, ∀ w ∈ W, X.ρ g w ∈ W) (h : W ≠ ⊥) : subIncl X W hW ≠ 0 := by
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  intro h0
  have := congrArg (fun φ => φ.hom.hom.hom ⟨w, hw⟩) h0
  exact hw0 this

/-- In a simple `FDRep`, a `G`-stable subspace is `⊥` or `⊤`. -/
theorem eq_bot_or_eq_top_of_simple (X : FDRep.{u} k G) [Simple X] (W : Submodule k X)
    (hW : ∀ g, ∀ w ∈ W, X.ρ g w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases h : W = ⊥
  · exact Or.inl h
  · right
    have := mono_subIncl X W hW
    have : IsIso (subIncl X W hW) := isIso_of_mono_of_nonzero (subIncl_ne_zero X W hW h)
    rw [eq_top_iff]
    intro x _
    obtain ⟨w, hw⟩ := (bijective_of_isIso (subIncl X W hW)).2 x
    rw [← hw, subIncl_apply]
    exact w.2

theorem injective_of_mono {Y X : FDRep.{u} k G} (f : Y ⟶ X) [Mono f] :
    Function.Injective f.hom.hom.hom := by
  have hK : ∀ g, ∀ y ∈ LinearMap.ker f.hom.hom.hom,
      Y.ρ g y ∈ LinearMap.ker f.hom.hom.hom := by
    intro g y hy
    rw [LinearMap.mem_ker] at hy ⊢
    have h := congrArg (fun m => m.hom.hom y) (f.comm g)
    change f.hom.hom.hom (Y.ρ g y) = X.ρ g (f.hom.hom.hom y) at h
    rw [h, hy, map_zero]
  have h0 : subIncl Y _ hK ≫ f = 0 := by
    ext ⟨y, hy⟩
    exact hy
  have : subIncl Y _ hK = 0 := (cancel_mono f).1 (h0.trans Limits.zero_comp.symm)
  have hbot : LinearMap.ker f.hom.hom.hom = ⊥ := by
    by_contra hne
    exact subIncl_ne_zero Y _ hK hne this
  exact LinearMap.ker_eq_bot.1 hbot

theorem nontrivial_of_simple (V : FDRep.{u} k G) [Simple V] : Nontrivial V := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply id_nonzero V
  ext x
  exact Subsingleton.elim _ _

/-- **The dual of a simple finite-dimensional representation is simple.** Any group `G`,
any field `k`; discharges the hypothesis `[Simple (π e)ᘁ]` of `lattice_support_rule`. -/
theorem dual_simple {k : Type u} {G : Type v} [Field k] [Group G]
    (V : FDRep k G) [Simple V] : Simple Vᘁ := by
  have hV := nontrivial_of_simple V
  refine ⟨fun {Y} f _ => ⟨fun hiso hf0 => ?_, fun hf0 => ?_⟩⟩
  · -- `Vᘁ ≠ 0` because `V` is nontrivial and finite-dimensional.
    obtain ⟨φ, hφ⟩ := exists_ne (0 : Module.Dual k V)
    obtain ⟨y, hy⟩ := (bijective_of_isIso f).2 φ
    apply hφ
    rw [← hy, hf0]
    rfl
  · let L : Y.V →ₗ[k] Module.Dual k V := f.hom.hom.hom
    let U : Submodule k (Module.Dual k V) := LinearMap.range L
    have hU : ∀ g, ∀ φ ∈ U, (show Module.Dual k V from (Vᘁ).ρ g φ) ∈ U := by
      rintro g _ ⟨y, rfl⟩
      refine ⟨Y.ρ g y, ?_⟩
      have h := congrArg (fun m => m.hom.hom y) (f.comm g)
      exact h
    let W : Submodule k V := U.dualCoannihilator
    have hW : ∀ g, ∀ w ∈ W, V.ρ g w ∈ W := by
      intro g w hw
      rw [Submodule.mem_dualCoannihilator] at hw ⊢
      intro φ hφ
      have := dual_ρ_apply V g⁻¹ φ w
      rw [inv_inv] at this
      rw [← this]
      exact hw _ (hU g⁻¹ φ hφ)
    rcases eq_bot_or_eq_top_of_simple V W hW with hbot | htop
    · have hUtop : U = ⊤ := by
        rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := U)]
        change W.dualAnnihilator = ⊤
        rw [hbot, Submodule.dualAnnihilator_bot]
      refine isIso_of_bijective f ⟨injective_of_mono f, ?_⟩
      intro φ
      have : (show Module.Dual k V from φ) ∈ U := hUtop ▸ Submodule.mem_top
      exact this
    · exfalso
      apply hf0
      have hL : L = 0 := by
        ext y x
        have hx : x ∈ W := htop ▸ Submodule.mem_top
        exact (Submodule.mem_dualCoannihilator x).1 hx (L y) ⟨y, rfl⟩
      ext y
      exact LinearMap.congr_fun hL y

/-- `dual_simple` as an instance, so `[Simple Vᘁ]` is found automatically. -/
instance instSimpleDual (V : FDRep.{u} k G) [Simple V] : Simple Vᘁ := dual_simple V

/-- `lattice_support_rule` with the dual-simplicity hypothesis discharged. -/
theorem lattice_support_rule_of_simple {Vx E : Type*} [Fintype E] (Γ : OrientedGraph Vx E)
    (π : E → FDRep k G) [hs : ∀ e, Simple (π e)]
    (hinv : ∀ v, Representation.invariants (vertexRep (incident Γ π v)).ρ ≠ ⊥) (v : Vx) :
    (∀ x, ntList (incident Γ π v) ≠ [x]) ∧
    (∀ x y, ntList (incident Γ π v) = [x, y] →
      (x.out = true → y.out = false → Nonempty (x.rep ≅ y.rep)) ∧
      (x.out = false → y.out = true → Nonempty (x.rep ≅ y.rep)) ∧
      (x.out = true → y.out = true → Nonempty (x.repᘁ ≅ y.rep)) ∧
      (x.out = false → y.out = false → Nonempty (x.rep ≅ y.repᘁ))) :=
  lattice_support_rule (hd := fun e => dual_simple (π e)) Γ π hinv v

end GaugeSupport

#print axioms GaugeSupport.dual_simple
#print axioms GaugeSupport.lattice_support_rule_of_simple

