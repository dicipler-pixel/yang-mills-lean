/-
GaugeSupportPeterWeylFinite.lean — `PeterWeylLinks` for every finite group over `ℂ`
(Grey, 2026-11-11).

Setting: `H = (E → G) → ℂ` (functions of the link variables), with the lattice gauge action
  `(g · ψ)(U) = ψ (e ↦ g (src e)⁻¹ * U e * g (tgt e))`   (`latticeGauge`, `latticeGauge_apply`).
Convention: this matches `edgeGauge`, which lets `g (src e)` act on `V` and `g (tgt e)` on `V*`.
The coefficient tensor `coeffTensor V u ∈ V ⊗ V*` is the element corresponding to `ρ(u)` under
`V ⊗ V* ≅ End V` (`v ⊗ φ ↦ (m ↦ φ m • v)`), and `(a, b)` acting on `V ⊗ V*` sends it to the
coefficient tensor of `a u b⁻¹` (`map_coeffTensor`). Hence the gauge permutation of the
configurations, `U ↦ (e ↦ g_src U_e g_tgt⁻¹)`, is matched exactly by `edgeGauge`.

* `fourierProj irr π ψ = ∑_U ψ(U) • ⊗_e coeffTensor (irr (π e)) (U e)` (unnormalised);
  `fourierProj_equivariant`.
* `IsCompleteIrrFamily irr` — the ONLY hypothesis on the family: every finite-dimensional
  irreducible complex representation of `G` is isomorphic (`Representation.Equiv`) to some
  `irr i`. Pairwise non-isomorphism and irreducibility of the members are not needed here
  (`Simple` is used only by the support-rule corollary).
* `fourierProj_separating`: separation, derived from Maschke (`IsSemisimpleModule ℂ[G] ℂ[G]`,
  Mathlib): elements of simple left ideals span `ℂ[G]`; each simple left ideal is an
  irreducible representation, hence receives an equivariant map from some `irr i`; this shows
  that the operator `∑_U ψ(U) ⊗_e (left mult. by U e)` on `⊗_e ℂ[G]` vanishes when all
  Fourier projections do, and that operator determines `ψ` (evaluate at `⊗_e 1`).
* `peterWeylLinks_of_finite`, `gauge_support_rule_links_finite`.
* `isCompleteIrrFamily_allReps`, `peterWeylLinks_of_finite_allReps`: the hypothesis is
  satisfiable (redundant family of all representations on `ℂⁿ`).
* `not_peterWeylLinks_trivial_only`, `not_isCompleteIrrFamily_trivial_S3`: with the trivial
  representation alone (for `S₃`: omitting sign and standard), `PeterWeylLinks` is false.
-/
import GaugeSupportReshuffleRep
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.Contraction

open CategoryTheory MonoidalCategory Module TensorProduct

namespace GaugeSupport

variable {G : Type} [Group G]

/-! ### Matrix coefficients as tensors in `V ⊗ V*` -/

section Coeff

variable (V : FDRep ℂ G)

/-- `V ⊗ V* ≃ End V`, `v ⊗ φ ↦ (m ↦ φ m • v)`. -/
noncomputable def coeffEquiv : ((V : Type) ⊗[ℂ] ((Vᘁ : FDRep ℂ G) : Type)) ≃ₗ[ℂ] (V →ₗ[ℂ] V) :=
  (TensorProduct.comm ℂ V (Module.Dual ℂ V)).trans (dualTensorHomEquiv ℂ V V)

theorem coeffEquiv_tmul (v : V) (φ : ((Vᘁ : FDRep ℂ G) : Type)) (m : V) :
    coeffEquiv V (v ⊗ₜ[ℂ] φ) m = (show Module.Dual ℂ V from φ) m • v := by
  simp [coeffEquiv, dualTensorHomEquiv]
  rfl

/-- The matrix-coefficient tensor of `u`: the element of `V ⊗ V*` corresponding to `ρ(u)`. -/
noncomputable def coeffTensor (u : G) : ((V : Type) ⊗[ℂ] ((Vᘁ : FDRep ℂ G) : Type)) :=
  (coeffEquiv V).symm (V.ρ u)

theorem coeffEquiv_map (a b : G) (t : (V : Type) ⊗[ℂ] ((Vᘁ : FDRep ℂ G) : Type)) :
    coeffEquiv V (TensorProduct.map (V.ρ a) ((Vᘁ).ρ b) t) =
      V.ρ a ∘ₗ coeffEquiv V t ∘ₗ V.ρ b⁻¹ := by
  induction t using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, LinearMap.zero_comp, LinearMap.comp_zero]
  | tmul v φ =>
    ext m
    rw [TensorProduct.map_tmul, coeffEquiv_tmul, LinearMap.comp_apply, LinearMap.comp_apply,
      coeffEquiv_tmul, map_smul]
    congr 1
    exact dual_ρ_apply V b φ m
  | add s t hs ht =>
    rw [map_add, map_add, hs, ht, map_add, LinearMap.add_comp, LinearMap.comp_add]

/-- **The coefficient tensor transforms correctly**: `(a, b)` acting on `V ⊗ V*` sends the
coefficient tensor of `u` to that of `a u b⁻¹`. -/
theorem map_coeffTensor (a b u : G) :
    TensorProduct.map (V.ρ a) ((Vᘁ).ρ b) (coeffTensor V u) = coeffTensor V (a * u * b⁻¹) := by
  apply (coeffEquiv V).injective
  rw [coeffEquiv_map, coeffTensor, coeffTensor, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply, map_mul, map_mul]
  rfl

/-- Evaluation of a coefficient tensor at a vector. -/
noncomputable def coeffEval (x : V) :
    ((V : Type) ⊗[ℂ] ((Vᘁ : FDRep ℂ G) : Type)) →ₗ[ℂ] V :=
  LinearMap.applyₗ x ∘ₗ (coeffEquiv V).toLinearMap

theorem coeffEval_coeffTensor (x : V) (u : G) : coeffEval V x (coeffTensor V u) = V.ρ u x := by
  show coeffEquiv V ((coeffEquiv V).symm (V.ρ u)) x = _
  rw [LinearEquiv.apply_symm_apply]

end Coeff

/-! ### The lattice space of a finite group and its Fourier projections -/

section Lattice

variable {Vx E : Type*} (Γ : OrientedGraph Vx E)

/-- The gauge action on link variables: `(g · U) e = g (src e) * U e * g (tgt e)⁻¹`. -/
def linkAct (g : Vx → G) (U : E → G) : E → G := fun e => g (Γ.src e) * U e * (g (Γ.tgt e))⁻¹

theorem linkAct_one (U : E → G) : linkAct Γ 1 U = U := by
  funext e; simp [linkAct]

theorem linkAct_mul (g h : Vx → G) (U : E → G) :
    linkAct Γ (g * h) U = linkAct Γ g (linkAct Γ h U) := by
  funext e; simp [linkAct, mul_assoc]

/-- `linkAct Γ g` as a permutation of the link configurations. -/
def linkPerm (g : Vx → G) : Equiv.Perm (E → G) where
  toFun := linkAct Γ g
  invFun := linkAct Γ g⁻¹
  left_inv U := by rw [← linkAct_mul, inv_mul_cancel, linkAct_one]
  right_inv U := by rw [← linkAct_mul, mul_inv_cancel, linkAct_one]

/-- **The lattice gauge action** on `H = (E → G) → ℂ`:
`(g · ψ)(U) = ψ (e ↦ g (src e)⁻¹ * U e * g (tgt e))`. -/
noncomputable def latticeGauge : Representation ℂ (Vx → G) ((E → G) → ℂ) where
  toFun g := LinearMap.funLeft ℂ ℂ (linkAct Γ g⁻¹)
  map_one' := by
    ext ψ U
    simp [LinearMap.funLeft_apply, linkAct_one]
  map_mul' g h := by
    ext ψ U
    simp only [LinearMap.funLeft_apply, Module.End.mul_apply, mul_inv_rev, linkAct_mul]

theorem latticeGauge_apply (g : Vx → G) (ψ : (E → G) → ℂ) (U : E → G) :
    latticeGauge Γ g ψ U = ψ (fun e => (g (Γ.src e))⁻¹ * U e * g (Γ.tgt e)) := by
  show ψ (linkAct Γ g⁻¹ U) = _
  congr 1
  funext e
  simp [linkAct]

variable [Fintype E] [DecidableEq E] [Fintype G] {Irr : Type*} (irr : Irr → FDRep ℂ G)

/-- The coefficient tensor of a link configuration in the block of a labelling `π`. -/
noncomputable def configTensor (π : E → Irr) (U : E → G) : EdgeBlock (irr ∘ π) :=
  PiTensorProduct.tprod ℂ (fun e => coeffTensor (irr (π e)) (U e))

/-- **Fourier projection**: `ψ ↦ ∑_U ψ(U) ⊗_e (coefficient tensor of U e in V ⊗ V*)`
(no normalisation; any nonzero factor per block would do). -/
noncomputable def fourierProj (π : E → Irr) : ((E → G) → ℂ) →ₗ[ℂ] EdgeBlock (irr ∘ π) where
  toFun ψ := ∑ U, ψ U • configTensor irr π U
  map_add' ψ φ := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c ψ := by simp [Finset.smul_sum, smul_smul]

theorem fourierProj_apply (π : E → Irr) (ψ : (E → G) → ℂ) :
    fourierProj irr π ψ = ∑ U, ψ U • configTensor irr π U := rfl

omit [Fintype E] [DecidableEq E] [Fintype G] in
theorem edgeGauge_configTensor (π : E → Irr) (g : Vx → G) (U : E → G) :
    edgeGauge Γ (irr ∘ π) g (configTensor irr π U) = configTensor irr π (linkAct Γ g U) := by
  rw [edgeGauge_apply, configTensor, PiTensorProduct.map_tprod]
  congr 1
  funext e
  exact map_coeffTensor (irr (π e)) _ _ _

/-- **The Fourier projections are gauge-equivariant.** -/
theorem fourierProj_equivariant (π : E → Irr) (g : Vx → G) (ψ : (E → G) → ℂ) :
    fourierProj irr π (latticeGauge Γ g ψ) = edgeGauge Γ (irr ∘ π) g (fourierProj irr π ψ) := by
  rw [fourierProj_apply, fourierProj_apply, map_sum]
  simp only [map_smul, edgeGauge_configTensor]
  rw [← Equiv.sum_comp (linkPerm Γ g)]
  refine Finset.sum_congr rfl fun U _ => ?_
  congr 1
  show ψ (linkAct Γ g⁻¹ (linkAct Γ g U)) = ψ U
  rw [← linkAct_mul, inv_mul_cancel, linkAct_one]

end Lattice

/-! ### Completeness of the irreducible family and Maschke -/

/-- **The only hypothesis on the family**: every finite-dimensional irreducible complex
representation of `G` is isomorphic to some `irr i`. (Pairwise non-isomorphism is not needed.) -/
def IsCompleteIrrFamily {Irr : Type*} (irr : Irr → FDRep ℂ G) : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W]
    (σ : Representation ℂ G W), σ.IsIrreducible → ∃ i, Nonempty (σ.Equiv (irr i).ρ)

section Maschke

variable [Fintype G] {Irr : Type*} (irr : Irr → FDRep ℂ G)

omit [Fintype G] in
/-- The inclusion of a left ideal of `ℂ[G]`, viewed as a `ℂ`-vector space, into `ℂ[G]`. -/
noncomputable def idealIncl (m : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)) :
    RestrictScalars ℂ (MonoidAlgebra ℂ G) m →ₗ[ℂ] MonoidAlgebra ℂ G where
  toFun z := (RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) m z).val
  map_add' _ _ := by simp
  map_smul' c z := by
    rw [RestrictScalars.addEquiv_map_smul, Submodule.coe_smul, Algebra.smul_def]
    rfl

omit [Fintype G] in
theorem idealIncl_injective (m : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)) :
    Function.Injective (idealIncl m) := fun _ _ h =>
  (RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) m).injective (Subtype.ext h)

set_option backward.isDefEq.respectTransparency false in
/-- Every element of a simple left ideal of `ℂ[G]` is hit by a `G`-equivariant map
from some `irr i`. -/
theorem exists_irr_map_of_simple (hIrr : IsCompleteIrrFamily irr)
    (m : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    [IsSimpleModule (MonoidAlgebra ℂ G) m] (w : MonoidAlgebra ℂ G) (hw : w ∈ m) :
    ∃ i, ∃ j : (irr i : Type) →ₗ[ℂ] MonoidAlgebra ℂ G, ∃ x, j x = w ∧
      ∀ (u : G) (y : irr i), MonoidAlgebra.single u 1 * j y = j ((irr i).ρ u y) := by
  have : Module.Finite ℂ (MonoidAlgebra ℂ G) := Module.Finite.of_basis (MonoidAlgebra.basis G ℂ)
  have : Module.Finite ℂ (RestrictScalars ℂ (MonoidAlgebra ℂ G) m) :=
    Module.Finite.of_injective (idealIncl m) (idealIncl_injective m)
  have hσ : (Representation.ofModule (k := ℂ) (G := G) m).IsIrreducible :=
    (Representation.isSimpleModule_iff_irreducible_ofModule m).1 inferInstance
  obtain ⟨i, ⟨φ⟩⟩ := hIrr _ _ hσ
  refine ⟨i, idealIncl m ∘ₗ φ.symm.toLinearMap, φ ((RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) m).symm ⟨w, hw⟩), ?_, ?_⟩
  · show idealIncl m (φ.symm (φ _)) = w
    rw [← Representation.Equiv.coe_symm]
    erw [LinearEquiv.symm_apply_apply]
    show ((RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) m)
      ((RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) m).symm ⟨w, hw⟩)).val = w
    rw [AddEquiv.apply_symm_apply]
  · intro u y
    show _ = idealIncl m (φ.symm ((irr i).ρ u y))
    have h := Representation.IntertwiningMap.isIntertwining _ _ φ.symm.toIntertwiningMap u y
    rw [Representation.Equiv.coe_toIntertwiningMap] at h
    rw [h]
    show _ * idealIncl m (φ.symm y) = _
    generalize φ.symm y = z
    rw [← Representation.asAlgebraHom_single_one, Representation.ofModule_asAlgebraHom_apply_apply]
    show _ = ((RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) m) ((RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) m).symm
      (MonoidAlgebra.single u 1 • RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) m z))).val
    rw [AddEquiv.apply_symm_apply, Submodule.coe_smul, smul_eq_mul]
    rfl

omit [Fintype G] in
/-- **Maschke**: the elements of simple left ideals of `ℂ[G]` span `ℂ[G]` over `ℂ`. -/
theorem span_simple_elements [Finite G] :
    Submodule.span ℂ {w : MonoidAlgebra ℂ G | ∃ m : Submodule (MonoidAlgebra ℂ G)
      (MonoidAlgebra ℂ G), IsSimpleModule (MonoidAlgebra ℂ G) m ∧ w ∈ m} = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ sSup {m : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G) |
      IsSimpleModule (MonoidAlgebra ℂ G) m} := by
    rw [IsSemisimpleModule.sSup_simples_eq_top (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)]
    trivial
  rw [sSup_eq_iSup'] at hx
  exact Submodule.iSup_induction (motive := fun y => y ∈ Submodule.span ℂ
      {w : MonoidAlgebra ℂ G | ∃ m : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G),
        IsSimpleModule (MonoidAlgebra ℂ G) m ∧ w ∈ m}) _ hx
    (fun m y hy => Submodule.subset_span ⟨m.1, m.2, hy⟩) (zero_mem _) (fun _ _ => add_mem)

/-- The "left regular" operator of `ψ` on `⨂_e ℂ[G]`: `∑_U ψ(U) ⊗_e (left mult. by U e)`. -/
noncomputable def regularOp {E : Type*} [Fintype E] [DecidableEq E] (ψ : (E → G) → ℂ) :
    (⨂[ℂ] _ : E, MonoidAlgebra ℂ G) →ₗ[ℂ] (⨂[ℂ] _ : E, MonoidAlgebra ℂ G) :=
  ∑ U, ψ U • PiTensorProduct.map (fun e => LinearMap.mulLeft ℂ (MonoidAlgebra.single (U e) 1))

theorem regularOp_tprod {E : Type*} [Fintype E] [DecidableEq E] (ψ : (E → G) → ℂ)
    (w : E → MonoidAlgebra ℂ G) :
    regularOp ψ (PiTensorProduct.tprod ℂ w) =
      ∑ U, ψ U • PiTensorProduct.tprod ℂ (fun e => MonoidAlgebra.single (U e) 1 * w e) := by
  simp [regularOp, LinearMap.sum_apply, PiTensorProduct.map_tprod]

/-- The regular operator determines `ψ`. -/
theorem eq_zero_of_regularOp_eq_zero {E : Type*} [Fintype E] [DecidableEq E] (ψ : (E → G) → ℂ)
    (h : regularOp ψ = 0) : ψ = 0 := by
  classical
  have h1 := congrArg (fun A => A (PiTensorProduct.tprod ℂ (fun _ : E => 1))) h
  simp only [regularOp_tprod, mul_one, LinearMap.zero_apply] at h1
  let B := Basis.piTensorProduct (fun _ : E => MonoidAlgebra.basis G ℂ)
  have hB : ∀ U : E → G, B U = PiTensorProduct.tprod ℂ (fun e => MonoidAlgebra.single (U e) 1) :=
    fun U => by rw [Basis.piTensorProduct_apply]; rfl
  simp only [← hB] at h1
  funext U
  exact Fintype.linearIndependent_iff.1 B.linearIndependent ψ h1 U

/-- **Separation**: if all Fourier projections of `ψ` vanish, then `ψ = 0`. -/
theorem fourierProj_separating {E : Type*} [Fintype E] [DecidableEq E]
    (hIrr : IsCompleteIrrFamily irr) (ψ : (E → G) → ℂ)
    (h : ∀ π : E → Irr, fourierProj irr π ψ = 0) : ψ = 0 := by
  classical
  apply eq_zero_of_regularOp_eq_zero
  let S := {w : MonoidAlgebra ℂ G | ∃ m : Submodule (MonoidAlgebra ℂ G)
      (MonoidAlgebra ℂ G), IsSimpleModule (MonoidAlgebra ℂ G) m ∧ w ∈ m}
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent ℂ S
  let B : Basis b ℂ (MonoidAlgebra ℂ G) :=
    Basis.mk hli (by rw [Subtype.range_coe, hspan, span_simple_elements])
  refine (Basis.piTensorProduct (fun _ : E => B)).ext fun c => ?_
  rw [Basis.piTensorProduct_apply, LinearMap.zero_apply]
  have hc : ∀ e, ∃ m : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G),
      IsSimpleModule (MonoidAlgebra ℂ G) m ∧ B (c e) ∈ m := fun e => by
    rw [Basis.mk_apply]; exact hbS (c e).2
  choose m hm hmem using hc
  have hj := fun e => @exists_irr_map_of_simple G _ _ Irr irr hIrr (m e) (hm e) _ (hmem e)
  choose i j x hjx hint using hj
  have hw : (fun e => B (c e)) = fun e => j e (x e) := funext fun e => (hjx e).symm
  rw [hw, regularOp_tprod]
  simp only [hint]
  have h0 := congrArg (PiTensorProduct.map (fun e => j e ∘ₗ coeffEval (irr (i e)) (x e))) (h i)
  rw [map_zero, fourierProj_apply, map_sum] at h0
  rw [← h0]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [map_smul, configTensor, PiTensorProduct.map_tprod]
  congr 2
  funext e
  rw [LinearMap.comp_apply, coeffEval_coeffTensor]

end Maschke

/-- The hypothesis is satisfiable: the (redundant) family of all representations on the
spaces `ℂⁿ` is complete. (Its members need not be irreducible; see `IsCompleteIrrFamily`.) -/
abbrev AllReps (G : Type) [Group G] := Σ n : ℕ, Representation ℂ G (Fin n → ℂ)

/-- The member of `AllReps` as an `FDRep`. -/
noncomputable abbrev allReps (G : Type) [Group G] (p : AllReps G) : FDRep ℂ G := FDRep.of p.2

theorem isCompleteIrrFamily_allReps : IsCompleteIrrFamily (allReps G) := by
  intro W _ _ _ σ _
  let e : W ≃ₗ[ℂ] (Fin (finrank ℂ W) → ℂ) := (Module.finBasis ℂ W).equivFun
  let σ' : Representation ℂ G (Fin (finrank ℂ W) → ℂ) :=
    { toFun := fun g => e.toLinearMap ∘ₗ σ g ∘ₗ e.symm.toLinearMap
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  refine ⟨⟨finrank ℂ W, σ'⟩, ⟨Representation.Equiv.mk e fun g => ?_⟩⟩
  refine LinearMap.ext fun w => ?_
  show e (σ g w) = e (σ g (e.symm (e w)))
  rw [LinearEquiv.symm_apply_apply]

/-! ### Main theorem -/

section Main

variable [Fintype G] {Vx E : Type*} [Fintype E] [DecidableEq E] (Γ : OrientedGraph Vx E)
  {Irr : Type*} (irr : Irr → FDRep ℂ G)

/-- **Peter–Weyl per link for every finite group** over `ℂ`: on `H = (E → G) → ℂ` with the
lattice gauge action `(g · ψ)(U) = ψ (e ↦ g (src e)⁻¹ * U e * g (tgt e))`, the Fourier
projections onto the link blocks `⊗_e (V_{π e} ⊗ V_{π e}*)` are gauge-equivariant and jointly
separating, for any complete family of irreducibles. -/
noncomputable def peterWeylLinksFinite (hIrr : IsCompleteIrrFamily irr) :
    PeterWeylLinks ℂ G Γ Irr irr ((E → G) → ℂ) (latticeGauge Γ) where
  proj := fourierProj irr
  proj_equivariant := fourierProj_equivariant Γ irr
  proj_separating := fourierProj_separating irr hIrr

theorem peterWeylLinks_of_finite (hIrr : IsCompleteIrrFamily irr) :
    Nonempty (PeterWeylLinks ℂ G Γ Irr irr ((E → G) → ℂ) (latticeGauge Γ)) :=
  ⟨peterWeylLinksFinite Γ irr hIrr⟩

theorem peterWeylLinksFinite_proj (hIrr : IsCompleteIrrFamily irr) :
    (peterWeylLinksFinite Γ irr hIrr).proj = fourierProj irr := rfl

/-- **The gauge support rule for finite groups, with no Peter–Weyl assumption**: for a gauge
invariant `ψ : (E → G) → ℂ` and a labelling `π` with nonzero Fourier component, the
nontrivial incident factors at every vertex obey the one- and two-leg rules. -/
theorem gauge_support_rule_links_finite [Fintype Vx] [DecidableEq Vx] [∀ i, Simple (irr i)]
    (hIrr : IsCompleteIrrFamily irr) (ψ : (E → G) → ℂ) (hψ : ∀ g, latticeGauge Γ g ψ = ψ)
    (π : E → Irr) (hπ : fourierProj irr π ψ ≠ 0) (v : Vx) :
    (∀ x, ntList (incident Γ (irr ∘ π) v) ≠ [x]) ∧
    (∀ x y, ntList (incident Γ (irr ∘ π) v) = [x, y] →
      (x.out = true → y.out = false → Nonempty (x.rep ≅ y.rep)) ∧
      (x.out = false → y.out = true → Nonempty (x.rep ≅ y.rep)) ∧
      (x.out = true → y.out = true → Nonempty (x.repᘁ ≅ y.rep)) ∧
      (x.out = false → y.out = false → Nonempty (x.rep ≅ y.repᘁ))) :=
  gauge_support_rule_links (peterWeylLinksFinite Γ irr hIrr) ψ hψ π hπ v

/-- With the family of all representations on `ℂⁿ`, Peter–Weyl per link holds with no
hypothesis at all. -/
theorem peterWeylLinks_of_finite_allReps :
    Nonempty (PeterWeylLinks ℂ G Γ (AllReps G) (allReps G) ((E → G) → ℂ) (latticeGauge Γ)) :=
  peterWeylLinks_of_finite Γ _ isCompleteIrrFamily_allReps

end Main

/-! ### The completeness hypothesis cannot be dropped -/

section Drop

/-- The trivial one-dimensional representation. -/
noncomputable abbrev trivFD (G : Type) [Group G] : FDRep ℂ G :=
  FDRep.of (Representation.trivial ℂ G ℂ)

/-- One link `() : 0 → 1`. -/
def oneLinkGraph : OrientedGraph (Fin 2) Unit := ⟨fun _ => 0, fun _ => 1⟩

theorem edgeGauge_trivFD {Vx E : Type*} [Fintype E] (Γ : OrientedGraph Vx E) (g : Vx → G)
    (t : EdgeBlock (fun _ : E => trivFD G)) : edgeGauge Γ (fun _ => trivFD G) g t = t := by
  rw [edgeGauge_apply]
  have h : (fun e => TensorProduct.map ((trivFD G).ρ (g (Γ.src e)))
      (((trivFD G)ᘁ : FDRep ℂ G).ρ (g (Γ.tgt e)))) = fun _ => LinearMap.id := by
    funext e
    apply TensorProduct.ext'
    intro x φ
    rw [TensorProduct.map_tmul, LinearMap.id_apply]
    congr 1
    apply LinearMap.ext
    intro y
    exact dual_ρ_apply (trivFD G) _ φ y
  rw [h, PiTensorProduct.map_id, LinearMap.id_apply]

/-- **Dropping irreducibles breaks Peter–Weyl**: for any group with a nontrivial element, the
family consisting of the trivial representation alone does not satisfy `PeterWeylLinks` on one
link with the lattice gauge action. -/
theorem not_peterWeylLinks_trivial_only (g₀ : G) (hg₀ : g₀ ≠ 1) :
    ¬ Nonempty (PeterWeylLinks ℂ G oneLinkGraph Unit (fun _ => trivFD G) ((Unit → G) → ℂ)
      (latticeGauge oneLinkGraph)) := by
  classical
  rintro ⟨PW⟩
  let ψ : (Unit → G) → ℂ := fun U => if U () = 1 then 1 else 0
  let g : Fin 2 → G := fun v => if v = 0 then g₀ else 1
  have hfix : latticeGauge oneLinkGraph g ψ - ψ = 0 := by
    apply PW.proj_separating
    intro π
    rw [map_sub, PW.proj_equivariant, sub_eq_zero]
    exact edgeGauge_trivFD oneLinkGraph g _
  have h1 := congrFun (sub_eq_zero.1 hfix) (fun _ => 1)
  rw [latticeGauge_apply] at h1
  simp [ψ, g, oneLinkGraph, hg₀] at h1

/-- The sign-free family `{trivial}` of `S₃` is not complete (it omits the sign and the
standard representation): otherwise `peterWeylLinks_of_finite` would contradict
`not_peterWeylLinks_trivial_only`. -/
theorem not_isCompleteIrrFamily_trivial_S3 :
    ¬ IsCompleteIrrFamily (fun _ : Unit => trivFD (Equiv.Perm (Fin 3))) := fun h =>
  not_peterWeylLinks_trivial_only (Equiv.swap 0 1) (by decide)
    (peterWeylLinks_of_finite oneLinkGraph _ h)

end Drop
end GaugeSupport

#print axioms GaugeSupport.map_coeffTensor
#print axioms GaugeSupport.fourierProj_equivariant
#print axioms GaugeSupport.exists_irr_map_of_simple
#print axioms GaugeSupport.span_simple_elements
#print axioms GaugeSupport.fourierProj_separating
#print axioms GaugeSupport.isCompleteIrrFamily_allReps
#print axioms GaugeSupport.peterWeylLinks_of_finite
#print axioms GaugeSupport.peterWeylLinks_of_finite_allReps
#print axioms GaugeSupport.gauge_support_rule_links_finite
#print axioms GaugeSupport.not_peterWeylLinks_trivial_only
#print axioms GaugeSupport.not_isCompleteIrrFamily_trivial_S3
