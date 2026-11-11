/-
CubeWilsonExistence.lean — the 4-cycle case of the cube support theorem is attained
(Grey, 2026-11-11).

`cube_gauge_support_finite` says a nonzero gauge-invariant Fourier component on the cube with
1 to 6 non-trivial links has exactly 4 or 6 of them, on a short cycle. This file shows the
case "4" really occurs, for every finite group `G` with a non-trivial character
`φ : G →* ℂˣ`, in particular for `S₃` with the sign character.

* Irrep: a 1-dimensional character `φ`. Its simple left ideal is explicit,
  `charIdeal φ = span {∑_g φ(g⁻¹) g}` (`charIdeal_simple`), and `G` acts on it by the scalar
  `φ` (`simpleIrr_charSI_ρ`). It is non-trivial as a label iff `φ ≠ 1`
  (`charSI_isEmpty_iso`, `charSI_one_iso`). For `S₃`: `signChar = sign`.
* Wilson loop: the face `0 → 1 → 3 → 2 → 0` of `cubeE`, links `0 = (0,1)`, `5 = (1,3)` run
  forwards and `1 = (2,3)`, `4 = (0,2)` run backwards (respecting the `cubeΓ` orientation):
  `wilson φ U = φ (U₀ U₅ U₁⁻¹ U₄⁻¹)`, the trace of the loop holonomy in the 1-dim rep.
  Gauge invariant (`wilson_gauge_invariant`).
* Labelling `faceπ φ`: `φ⁻¹` on links 0, 5, `φ` on links 1, 4, trivial elsewhere.
  `fourierProj simpleIrr (faceπ φ) (wilson φ) ≠ 0` (`fourierProj_wilson_ne_zero`, by a
  product of per-link functionals: every term contributes the same nonzero number) and
  exactly 4 non-trivial links (`faceπ_card`).
* Negation of the control: with the trivial character the labelling has 0 non-trivial links
  (`faceπ_one_card`, `cube_wilson_trivial_card_S3`).

Option disclosure: `backward.isDefEq.respectTransparency false` on one declaration
(`charSI_one_iso`), for the `Module ℂ (RestrictScalars …)` instance on the ideal.
No `sorry`, no `native_decide`, no new axioms.
-/
import CubeFiniteUnconditional

open CategoryTheory MonoidalCategory TailFloor GaugeSupport NtListSupport PermCube
open scoped Classical

namespace GaugeSupport

section Char

variable {G : Type} [Group G] [Fintype G] (φ : G →* ℂˣ)

/-- The eigenvector of a character `φ` in `ℂ[G]`: `∑_g φ(g⁻¹) g`. -/
noncomputable def eChar : MonoidAlgebra ℂ G :=
  ∑ g, ((φ g⁻¹ : ℂˣ) : ℂ) • MonoidAlgebra.single g 1

theorem single_mul_eChar (u : G) :
    MonoidAlgebra.single u 1 * eChar φ = ((φ u : ℂˣ) : ℂ) • eChar φ := by
  rw [eChar, Finset.mul_sum, Finset.smul_sum]
  simp only [mul_smul_comm, MonoidAlgebra.single_mul_single, one_mul, smul_smul]
  rw [← Equiv.sum_comp (Equiv.mulLeft u⁻¹)]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [Equiv.coe_mulLeft, mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul,
    map_mul, Units.val_mul]
  ring_nf

theorem eChar_ne_zero : eChar φ ≠ 0 := by
  intro h
  have hli := (MonoidAlgebra.basis G ℂ).linearIndependent
  have hsum : ∑ g, ((φ g⁻¹ : ℂˣ) : ℂ) • MonoidAlgebra.basis G ℂ g = 0 := by
    simpa [eChar] using h
  have := Fintype.linearIndependent_iff.1 hli _ hsum 1
  simp at this

theorem mul_eChar_mem (r : MonoidAlgebra ℂ G) : ∃ c : ℂ, r * eChar φ = c • eChar φ := by
  induction r using MonoidAlgebra.induction_linear with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [add_mul, ha, hb, add_smul]⟩
  | single g c =>
    refine ⟨c * (φ g : ℂ), ?_⟩
    have : MonoidAlgebra.single g c = c • MonoidAlgebra.single g (1 : ℂ) := by
      rw [MonoidAlgebra.smul_single', mul_one]
    rw [this, smul_mul_assoc, single_mul_eChar, smul_smul]

/-- The left ideal spanned by `eChar φ`. -/
noncomputable def charIdeal : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G) :=
  Submodule.span (MonoidAlgebra ℂ G) {eChar φ}

theorem mem_charIdeal {z : MonoidAlgebra ℂ G} (hz : z ∈ charIdeal φ) :
    ∃ c : ℂ, z = c • eChar φ := by
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hz
  obtain ⟨c, hc⟩ := mul_eChar_mem φ r
  exact ⟨c, by rw [smul_eq_mul, hc]⟩

theorem charIdeal_simple : IsSimpleModule (MonoidAlgebra ℂ G) (charIdeal φ) := by
  rw [isSimpleModule_iff_isAtom]
  refine ⟨?_, fun N hN => ?_⟩
  · rw [charIdeal, Ne, Submodule.span_singleton_eq_bot]
    exact eChar_ne_zero φ
  · by_contra hne
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨c, rfl⟩ := mem_charIdeal φ (hN.le hx)
    have hc : c ≠ 0 := by rintro rfl; simp at hx0
    have he : eChar φ ∈ N := by
      have := N.smul_mem (algebraMap ℂ (MonoidAlgebra ℂ G) c⁻¹) hx
      rwa [algebraMap_smul, smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    exact hN.ne (le_antisymm hN.le ((Submodule.span_singleton_le_iff_mem _ _).2 he))

/-- The simple left ideal of a character. -/
noncomputable def charSI : SimpleIdeal G := ⟨charIdeal φ, charIdeal_simple φ⟩

/-- The generator of `charIdeal φ`, as a vector of the representation. -/
noncomputable def charVec : RestrictScalars ℂ (MonoidAlgebra ℂ G) (charIdeal φ) :=
  (RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) (charIdeal φ)).symm
    ⟨eChar φ, Submodule.mem_span_singleton_self _⟩

theorem idealIncl_charVec : idealIncl (charIdeal φ) (charVec φ) = eChar φ := by
  show ((RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) (charIdeal φ))
    ((RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) (charIdeal φ)).symm _)).val = _
  rw [AddEquiv.apply_symm_apply]

theorem charVec_ne_zero : charVec φ ≠ 0 := by
  intro h
  apply eChar_ne_zero φ
  rw [← idealIncl_charVec, h, map_zero]

/-- `G` acts on `charIdeal φ` by the scalar `φ`. -/
theorem ofModule_charIdeal (u : G) (z : RestrictScalars ℂ (MonoidAlgebra ℂ G) (charIdeal φ)) :
    Representation.ofModule (k := ℂ) (G := G) (charIdeal φ) u z = ((φ u : ℂˣ) : ℂ) • z := by
  apply idealIncl_injective
  rw [idealIncl_ofModule, map_smul]
  obtain ⟨c, hc⟩ := mem_charIdeal φ (RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) _ z).2
  change MonoidAlgebra.single u 1 * (RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) _ z).val =
    _ • (RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) _ z).val
  rw [hc, mul_smul_comm, single_mul_eChar, smul_comm]

theorem simpleIrr_charSI_ρ (u : G) (z : simpleIrr (charSI φ)) :
    (simpleIrr (charSI φ)).ρ u z = ((φ u : ℂˣ) : ℂ) • z := by
  have h := congrArg (fun r => r u z) (simpleIrr_ρ (charSI φ))
  exact h.trans (ofModule_charIdeal φ u z)

/-- A non-trivial character gives a non-trivial label. -/
theorem charSI_isEmpty_iso (g₀ : G) (hg₀ : φ g₀ ≠ 1) :
    IsEmpty (𝟙_ (FDRep ℂ G) ≅ simpleIrr (charSI φ)) := by
  refine ⟨fun i => ?_⟩
  let f := FDRep.isoToLinearEquiv i
  let one : (𝟙_ (FDRep ℂ G)).V := (1 : ℂ)
  have h := isoToLinearEquiv_ρ i g₀ one
  have h1 : (𝟙_ (FDRep ℂ G)).ρ g₀ one = one := rfl
  rw [h1, simpleIrr_charSI_ρ] at h
  have h2 : (((φ g₀ : ℂˣ) : ℂ) - 1) • f one = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
  rcases smul_eq_zero.1 h2 with h3 | h3
  · apply hg₀
    ext
    simpa [sub_eq_zero] using h3
  · have : one = 0 := f.injective (h3.trans (map_zero f).symm)
    exact one_ne_zero (α := ℂ) this

theorem eq_smul_charVec (z : RestrictScalars ℂ (MonoidAlgebra ℂ G) (charIdeal φ)) :
    ∃ c : ℂ, z = c • charVec φ := by
  obtain ⟨c, hc⟩ := mem_charIdeal φ (RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) _ z).2
  refine ⟨c, idealIncl_injective _ ?_⟩
  rw [map_smul, idealIncl_charVec]
  exact hc

set_option backward.isDefEq.respectTransparency false in
/-- The trivial character gives a trivial label: `𝟙 ≅ simpleIrr (charSI 1)`. -/
theorem charSI_one_iso : Nonempty (𝟙_ (FDRep ℂ G) ≅ simpleIrr (charSI (1 : G →* ℂˣ))) := by
  let L : ℂ →ₗ[ℂ] simpleIrr (charSI (1 : G →* ℂˣ)) :=
    LinearMap.toSpanSingleton ℂ _ (charVec 1)
  let T : 𝟙_ (FDRep ℂ G) ⟶ simpleIrr (charSI (1 : G →* ℂˣ)) :=
    ⟨InducedCategory.homMk (ModuleCat.ofHom L), fun g => by
      ext
      change L 1 = (simpleIrr (charSI (1 : G →* ℂˣ))).ρ g (L 1)
      rw [simpleIrr_charSI_ρ]
      simp⟩
  have hT : Function.Bijective T.hom.hom.hom := by
    refine ⟨fun x y hxy => ?_, fun z => ?_⟩
    · have hxy' : L x = L y := hxy
      exact smul_left_injective ℂ (charVec_ne_zero 1) hxy'
    · obtain ⟨c, hc⟩ := eq_smul_charVec (1 : G →* ℂˣ) z
      exact ⟨c, (show L c = z from hc.symm)⟩
  have := isIso_of_bijective T hT
  exact ⟨asIso T⟩

/-- `charVec φ` viewed in the carrier of `simpleIrr (charSI φ)`. -/
noncomputable def charVecV : simpleIrr (charSI φ) := charVec φ

theorem charVecV_ne_zero : charVecV φ ≠ 0 := charVec_ne_zero φ

theorem dual_coeffTensor_charSI (d : Module.Dual ℂ (simpleIrr (charSI φ))) (u : G) :
    d (coeffEval (simpleIrr (charSI φ)) (charVecV φ) (coeffTensor (simpleIrr (charSI φ)) u)) =
      ((φ u : ℂˣ) : ℂ) * d (charVecV φ) := by
  rw [coeffEval_coeffTensor, simpleIrr_charSI_ρ, map_smul, smul_eq_mul]

theorem exists_dual_charVecV :
    ∃ d : Module.Dual ℂ (simpleIrr (charSI φ)), d (charVecV φ) ≠ 0 := by
  by_contra h
  push Not at h
  exact charVecV_ne_zero φ ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 h)

end Char

/-! ### A Wilson loop on one face of the cube -/

section Wilson

open scoped TensorProduct

variable {G : Type} [Group G] [Fintype G] (φ : G →* ℂˣ)

/-- Labels: the face `0 → 1 → 3 → 2 → 0` (links `0 = (0,1)`, `5 = (1,3)`, `1 = (2,3)`,
`4 = (0,2)` of `cubeE`) carries `φ⁻¹` on the two links run forwards and `φ` on the two run
backwards; every other link carries the trivial character. -/
def faceLabel (e : Fin 12) : G →* ℂˣ :=
  if e = 0 ∨ e = 5 then φ⁻¹ else if e = 1 ∨ e = 4 then φ else 1

/-- The labelling by simple left ideals. -/
noncomputable def faceπ (e : Fin 12) : SimpleIdeal G := charSI (faceLabel φ e)

/-- The Wilson loop of `φ` around the face: `φ (U₀ U₅ U₁⁻¹ U₄⁻¹)`. -/
def wilson (U : Fin 12 → G) : ℂ := ((φ (U 0 * U 5 * (U 1)⁻¹ * (U 4)⁻¹) : ℂˣ) : ℂ)

omit [Fintype G] in
/-- **The Wilson loop is gauge invariant.** -/
theorem wilson_gauge_invariant (g : Fin 8 → G) : latticeGauge cubeΓ g (wilson φ) = wilson φ := by
  funext U
  rw [latticeGauge_apply]
  have hs0 : cubeΓ.src 0 = 0 := by decide
  have ht0 : cubeΓ.tgt 0 = 1 := by decide
  have hs5 : cubeΓ.src 5 = 1 := by decide
  have ht5 : cubeΓ.tgt 5 = 3 := by decide
  have hs1 : cubeΓ.src 1 = 2 := by decide
  have ht1 : cubeΓ.tgt 1 = 3 := by decide
  have hs4 : cubeΓ.src 4 = 0 := by decide
  have ht4 : cubeΓ.tgt 4 = 2 := by decide
  simp only [wilson, hs0, ht0, hs5, ht5, hs1, ht1, hs4, ht4]
  have hW : (g 0)⁻¹ * U 0 * g 1 * ((g 1)⁻¹ * U 5 * g 3) * ((g 2)⁻¹ * U 1 * g 3)⁻¹ *
      ((g 0)⁻¹ * U 4 * g 2)⁻¹ = (g 0)⁻¹ * (U 0 * U 5 * (U 1)⁻¹ * (U 4)⁻¹) * g 0 := by group
  rw [hW, map_mul, map_mul, map_inv, mul_comm _ (φ (g 0)), ← mul_assoc, mul_inv_cancel, one_mul]

omit [Fintype G] in
theorem wilson_mul_labels (U : Fin 12 → G) :
    wilson φ U * ∏ e, ((faceLabel φ e (U e) : ℂˣ) : ℂ) = 1 := by
  have h : φ (U 0 * U 5 * (U 1)⁻¹ * (U 4)⁻¹) * ∏ e, faceLabel φ e (U e) = 1 := by
    simp [Fin.prod_univ_succ, faceLabel]
    generalize φ (U 0) = a, φ (U 1) = b, φ (U 4) = c, φ (U 5) = d
    rw [← Units.val_eq_one]
    push_cast
    field_simp
  have := congrArg Units.val h
  push_cast at this
  exact this

/-- **Non-vanishing**: the Wilson loop has a non-zero Fourier component at the face
labelling. -/
theorem fourierProj_wilson_ne_zero :
    fourierProj simpleIrr (faceπ φ) (wilson φ) ≠ 0 := by
  have hd := fun e => exists_dual_charVecV (faceLabel φ e)
  choose d hd using hd
  let L : ∀ e, ((simpleIrr (faceπ φ e) : Type) ⊗[ℂ] ((simpleIrr (faceπ φ e))ᘁ : FDRep ℂ G))
      →ₗ[ℂ] ℂ := fun e =>
    d e ∘ₗ coeffEval (simpleIrr (charSI (faceLabel φ e))) (charVecV (faceLabel φ e))
  let Φ := PiTensorProduct.lift (MultilinearMap.mkPiAlgebra ℂ (Fin 12) ℂ) ∘ₗ
    PiTensorProduct.map L
  intro h
  have h0 := congrArg Φ h
  rw [map_zero, fourierProj_apply, map_sum] at h0
  have hterm : ∀ U, Φ (wilson φ U • configTensor simpleIrr (faceπ φ) U) =
      ∏ e, d e (charVecV (faceLabel φ e)) := by
    intro U
    rw [map_smul, configTensor, LinearMap.comp_apply, PiTensorProduct.map_tprod,
      PiTensorProduct.lift.tprod, MultilinearMap.mkPiAlgebra_apply]
    have hL : ∀ e, L e (coeffTensor (simpleIrr (faceπ φ e)) (U e)) =
        ((faceLabel φ e (U e) : ℂˣ) : ℂ) * d e (charVecV (faceLabel φ e)) := fun e =>
      dual_coeffTensor_charSI (faceLabel φ e) (d e) (U e)
    simp only [hL]
    rw [Finset.prod_mul_distrib, smul_eq_mul, ← mul_assoc, wilson_mul_labels, one_mul]
  simp only [hterm, Finset.sum_const, Finset.card_univ] at h0
  rcases smul_eq_zero.1 h0 with h1 | h1
  · exact Fintype.card_ne_zero h1
  · exact (Finset.prod_ne_zero_iff.2 fun e _ => hd e) h1

theorem not_NTe_charSI_one :
    ¬ IsEmpty (𝟙_ (FDRep ℂ G) ≅ simpleIrr (charSI (1 : G →* ℂˣ))) :=
  fun h => h.false (charSI_one_iso (G := G)).some

theorem NTe_faceπ_iff (g₀ : G) (hg₀ : φ g₀ ≠ 1) (e : Fin 12) :
    NTe (simpleIrr ∘ faceπ φ) e ↔ e ∈ ({0, 1, 4, 5} : Finset (Fin 12)) := by
  have hinv : (φ⁻¹) g₀ ≠ 1 := by rw [MonoidHom.inv_apply]; exact inv_ne_one.2 hg₀
  have hN := charSI_isEmpty_iso φ g₀ hg₀
  have hNi := charSI_isEmpty_iso φ⁻¹ g₀ hinv
  have hT := not_NTe_charSI_one (G := G)
  fin_cases e <;> simp [NTe, faceπ, faceLabel, hN, hNi, hT]

/-- **Exactly four non-trivial links**: the face labelling is non-trivial on precisely the
four face links. -/
theorem faceπ_card (g₀ : G) (hg₀ : φ g₀ ≠ 1) :
    (Finset.univ.filter (NTe (simpleIrr ∘ faceπ φ))).card = 4 := by
  have : Finset.univ.filter (NTe (simpleIrr ∘ faceπ φ)) = {0, 1, 4, 5} := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact NTe_faceπ_iff φ g₀ hg₀ e
  rw [this]
  rfl

/-- **Negation of the control**: with the trivial character the same face labelling has
no non-trivial link at all. -/
theorem faceπ_one_card :
    (Finset.univ.filter (NTe (simpleIrr ∘ faceπ (1 : G →* ℂˣ)))).card = 0 := by
  have hT := not_NTe_charSI_one (G := G)
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e _
  have h1 : faceLabel (1 : G →* ℂˣ) e = 1 := by
    unfold faceLabel; split_ifs <;> rfl
  simp only [NTe, Function.comp, faceπ, h1]
  exact hT

/-- **The 4-cycle case is attained on the cube** for every finite group with a non-trivial
character `φ : G →* ℂˣ`. -/
theorem cube_four_cycle_attained (g₀ : G) (hg₀ : φ g₀ ≠ 1) :
    ∃ ψ : (Fin 12 → G) → ℂ, (∀ g, latticeGauge cubeΓ g ψ = ψ) ∧
      ∃ π : Fin 12 → SimpleIdeal G, fourierProj simpleIrr π ψ ≠ 0 ∧
        (Finset.univ.filter (NTe (simpleIrr ∘ π))).card = 4 :=
  ⟨wilson φ, wilson_gauge_invariant φ, faceπ φ, fourierProj_wilson_ne_zero φ,
    faceπ_card φ g₀ hg₀⟩

/-- The same, with the short-cycle conclusion of `cube_gauge_support_finite`. -/
theorem cube_four_cycle_attained_shortCycle (g₀ : G) (hg₀ : φ g₀ ≠ 1) :
    ∃ ψ : (Fin 12 → G) → ℂ, (∀ g, latticeGauge cubeΓ g ψ = ψ) ∧
      ∃ π : Fin 12 → SimpleIdeal G, fourierProj simpleIrr π ψ ≠ 0 ∧
        (Finset.univ.filter (NTe (simpleIrr ∘ π))).card = 4 ∧
        shortCycle (supportList cubeΓ (simpleIrr ∘ π) Fin.val) = true := by
  refine ⟨wilson φ, wilson_gauge_invariant φ, faceπ φ, fourierProj_wilson_ne_zero φ,
    faceπ_card φ g₀ hg₀, ?_⟩
  exact cube_gauge_support_shortCycle_finite (wilson φ) (wilson_gauge_invariant φ) (faceπ φ)
    (fourierProj_wilson_ne_zero φ) (by rw [faceπ_card φ g₀ hg₀]; omega)
    (by rw [faceπ_card φ g₀ hg₀]; omega)

end Wilson

/-! ### `S₃` and the sign character -/

/-- The sign character of `S₃`, valued in `ℂˣ`. -/
noncomputable def signChar : S3 →* ℂˣ :=
  (Units.map (Int.castRingHom ℂ).toMonoidHom).comp Equiv.Perm.sign

theorem signChar_swap : signChar (Equiv.swap 0 1) ≠ 1 := by
  intro h
  have h2 := congrArg Units.val h
  simp [signChar] at h2
  norm_num at h2

/-- **The 4-cycle case is attained on the cube for `S₃`** (sign character on one face). -/
theorem cube_four_cycle_attained_S3 :
    ∃ ψ : (Fin 12 → S3) → ℂ, (∀ g, latticeGauge cubeΓ g ψ = ψ) ∧
      ∃ π : Fin 12 → SimpleIdeal S3, fourierProj simpleIrr π ψ ≠ 0 ∧
        (Finset.univ.filter (NTe (simpleIrr ∘ π))).card = 4 :=
  cube_four_cycle_attained signChar (Equiv.swap 0 1) signChar_swap

theorem cube_four_cycle_attained_S3_shortCycle :
    ∃ ψ : (Fin 12 → S3) → ℂ, (∀ g, latticeGauge cubeΓ g ψ = ψ) ∧
      ∃ π : Fin 12 → SimpleIdeal S3, fourierProj simpleIrr π ψ ≠ 0 ∧
        (Finset.univ.filter (NTe (simpleIrr ∘ π))).card = 4 ∧
        shortCycle (supportList cubeΓ (simpleIrr ∘ π) Fin.val) = true :=
  cube_four_cycle_attained_shortCycle signChar (Equiv.swap 0 1) signChar_swap

/-- The trivial labelling of the `S₃` face loop has no non-trivial link. -/
theorem cube_wilson_trivial_card_S3 :
    (Finset.univ.filter (NTe (simpleIrr ∘ faceπ (1 : S3 →* ℂˣ)))).card = 0 :=
  faceπ_one_card

end GaugeSupport

#print axioms GaugeSupport.single_mul_eChar
#print axioms GaugeSupport.eChar_ne_zero
#print axioms GaugeSupport.mul_eChar_mem
#print axioms GaugeSupport.mem_charIdeal
#print axioms GaugeSupport.charIdeal_simple
#print axioms GaugeSupport.idealIncl_charVec
#print axioms GaugeSupport.charVec_ne_zero
#print axioms GaugeSupport.ofModule_charIdeal
#print axioms GaugeSupport.simpleIrr_charSI_ρ
#print axioms GaugeSupport.charSI_isEmpty_iso
#print axioms GaugeSupport.eq_smul_charVec
#print axioms GaugeSupport.charSI_one_iso
#print axioms GaugeSupport.charVecV_ne_zero
#print axioms GaugeSupport.dual_coeffTensor_charSI
#print axioms GaugeSupport.exists_dual_charVecV
#print axioms GaugeSupport.wilson_gauge_invariant
#print axioms GaugeSupport.wilson_mul_labels
#print axioms GaugeSupport.fourierProj_wilson_ne_zero
#print axioms GaugeSupport.not_NTe_charSI_one
#print axioms GaugeSupport.NTe_faceπ_iff
#print axioms GaugeSupport.faceπ_card
#print axioms GaugeSupport.faceπ_one_card
#print axioms GaugeSupport.cube_four_cycle_attained
#print axioms GaugeSupport.cube_four_cycle_attained_shortCycle
#print axioms GaugeSupport.signChar_swap
#print axioms GaugeSupport.cube_four_cycle_attained_S3
#print axioms GaugeSupport.cube_four_cycle_attained_S3_shortCycle
#print axioms GaugeSupport.cube_wilson_trivial_card_S3
