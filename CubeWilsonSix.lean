/-
CubeWilsonSix.lean — the 6-cycle case of the cube support theorem is attained
(Grey, 2026-11-11).

Reuses the character construction of `CubeWilsonExistence` (`charSI φ`, `charVecV φ`,
`simpleIrr_charSI_ρ`, `charSI_isEmpty_iso`, `charSI_one_iso`) for a finite group `G` with a
non-trivial character `φ : G →* ℂˣ` (for `S₃`, the sign).

* Cycle: the boundary of the union of the two adjacent faces `{0,1,3,2}` and `{0,1,5,4}`
  (shared link `0 = (0,1)` dropped): `0 → 4 → 5 → 1 → 3 → 2 → 0`, i.e. links
  `8 = (0,4)` forwards, `2 = (4,5)` forwards, `9 = (1,5)` backwards, `5 = (1,3)` forwards,
  `1 = (2,3)` backwards, `4 = (0,2)` backwards (orientations of `cubeΓ`).
* `wilson6 φ U = φ (U₈ U₂ U₉⁻¹ U₅ U₁⁻¹ U₄⁻¹)`, gauge invariant.
* Labelling `face6π φ`: `φ⁻¹` on the forward links 8, 2, 5, `φ` on the backward links 9, 1, 4,
  trivial elsewhere. `fourierProj ≠ 0` and exactly 6 non-trivial links.
* `cube_four_and_six_attained_S3`: both cases of `cube_gauge_support_card_S3` occur.

No set_option, no `sorry`, no `native_decide`, no new axioms.
-/
import CubeWilsonExistence

open CategoryTheory MonoidalCategory TailFloor GaugeSupport NtListSupport PermCube
open scoped Classical TensorProduct

namespace GaugeSupport

section WilsonSix

variable {G : Type} [Group G] [Fintype G] (φ : G →* ℂˣ)

/-- Labels on the 6-cycle `0 → 4 → 5 → 1 → 3 → 2 → 0`: `φ⁻¹` on the links run forwards
(8, 2, 5), `φ` on the links run backwards (9, 1, 4), trivial elsewhere. -/
def face6Label (e : Fin 12) : G →* ℂˣ :=
  if e = 8 ∨ e = 2 ∨ e = 5 then φ⁻¹ else if e = 9 ∨ e = 1 ∨ e = 4 then φ else 1

/-- The 6-cycle labelling by simple left ideals. -/
noncomputable def face6π (e : Fin 12) : SimpleIdeal G := charSI (face6Label φ e)

/-- The Wilson loop of `φ` around the 6-cycle: `φ (U₈ U₂ U₉⁻¹ U₅ U₁⁻¹ U₄⁻¹)`. -/
def wilson6 (U : Fin 12 → G) : ℂ :=
  ((φ (U 8 * U 2 * (U 9)⁻¹ * U 5 * (U 1)⁻¹ * (U 4)⁻¹) : ℂˣ) : ℂ)

omit [Fintype G] in
/-- **The 6-cycle Wilson loop is gauge invariant.** -/
theorem wilson6_gauge_invariant (g : Fin 8 → G) :
    latticeGauge cubeΓ g (wilson6 φ) = wilson6 φ := by
  funext U
  rw [latticeGauge_apply]
  have hs8 : cubeΓ.src 8 = 0 := by decide
  have ht8 : cubeΓ.tgt 8 = 4 := by decide
  have hs2 : cubeΓ.src 2 = 4 := by decide
  have ht2 : cubeΓ.tgt 2 = 5 := by decide
  have hs9 : cubeΓ.src 9 = 1 := by decide
  have ht9 : cubeΓ.tgt 9 = 5 := by decide
  have hs5 : cubeΓ.src 5 = 1 := by decide
  have ht5 : cubeΓ.tgt 5 = 3 := by decide
  have hs1 : cubeΓ.src 1 = 2 := by decide
  have ht1 : cubeΓ.tgt 1 = 3 := by decide
  have hs4 : cubeΓ.src 4 = 0 := by decide
  have ht4 : cubeΓ.tgt 4 = 2 := by decide
  simp only [wilson6, hs8, ht8, hs2, ht2, hs9, ht9, hs5, ht5, hs1, ht1, hs4, ht4]
  have hW : (g 0)⁻¹ * U 8 * g 4 * ((g 4)⁻¹ * U 2 * g 5) * ((g 1)⁻¹ * U 9 * g 5)⁻¹ *
      ((g 1)⁻¹ * U 5 * g 3) * ((g 2)⁻¹ * U 1 * g 3)⁻¹ * ((g 0)⁻¹ * U 4 * g 2)⁻¹ =
      (g 0)⁻¹ * (U 8 * U 2 * (U 9)⁻¹ * U 5 * (U 1)⁻¹ * (U 4)⁻¹) * g 0 := by group
  rw [hW, map_mul, map_mul, map_inv, mul_comm _ (φ (g 0)), ← mul_assoc, mul_inv_cancel, one_mul]

omit [Fintype G] in
theorem wilson6_mul_labels (U : Fin 12 → G) :
    wilson6 φ U * ∏ e, ((face6Label φ e (U e) : ℂˣ) : ℂ) = 1 := by
  have h : φ (U 8 * U 2 * (U 9)⁻¹ * U 5 * (U 1)⁻¹ * (U 4)⁻¹) *
      ∏ e, face6Label φ e (U e) = 1 := by
    simp [Fin.prod_univ_succ, face6Label]
    generalize φ (U 1) = a, φ (U 2) = b, φ (U 4) = c, φ (U 5) = d, φ (U 8) = x, φ (U 9) = y
    rw [← Units.val_eq_one]
    push_cast
    field_simp
  have := congrArg Units.val h
  push_cast at this
  exact this

/-- **Non-vanishing**: the 6-cycle Wilson loop has a non-zero Fourier component at the
6-cycle labelling. -/
theorem fourierProj_wilson6_ne_zero :
    fourierProj simpleIrr (face6π φ) (wilson6 φ) ≠ 0 := by
  have hd := fun e => exists_dual_charVecV (face6Label φ e)
  choose d hd using hd
  let L : ∀ e, ((simpleIrr (face6π φ e) : Type) ⊗[ℂ] ((simpleIrr (face6π φ e))ᘁ : FDRep ℂ G))
      →ₗ[ℂ] ℂ := fun e =>
    d e ∘ₗ coeffEval (simpleIrr (charSI (face6Label φ e))) (charVecV (face6Label φ e))
  let Φ := PiTensorProduct.lift (MultilinearMap.mkPiAlgebra ℂ (Fin 12) ℂ) ∘ₗ
    PiTensorProduct.map L
  intro h
  have h0 := congrArg Φ h
  rw [map_zero, fourierProj_apply, map_sum] at h0
  have hterm : ∀ U, Φ (wilson6 φ U • configTensor simpleIrr (face6π φ) U) =
      ∏ e, d e (charVecV (face6Label φ e)) := by
    intro U
    rw [map_smul, configTensor, LinearMap.comp_apply, PiTensorProduct.map_tprod,
      PiTensorProduct.lift.tprod, MultilinearMap.mkPiAlgebra_apply]
    have hL : ∀ e, L e (coeffTensor (simpleIrr (face6π φ e)) (U e)) =
        ((face6Label φ e (U e) : ℂˣ) : ℂ) * d e (charVecV (face6Label φ e)) := fun e =>
      dual_coeffTensor_charSI (face6Label φ e) (d e) (U e)
    simp only [hL]
    rw [Finset.prod_mul_distrib, smul_eq_mul, ← mul_assoc, wilson6_mul_labels, one_mul]
  simp only [hterm, Finset.sum_const, Finset.card_univ] at h0
  rcases smul_eq_zero.1 h0 with h1 | h1
  · exact Fintype.card_ne_zero h1
  · exact (Finset.prod_ne_zero_iff.2 fun e _ => hd e) h1

theorem NTe_face6π_iff (g₀ : G) (hg₀ : φ g₀ ≠ 1) (e : Fin 12) :
    NTe (simpleIrr ∘ face6π φ) e ↔ e ∈ ({1, 2, 4, 5, 8, 9} : Finset (Fin 12)) := by
  have hinv : (φ⁻¹) g₀ ≠ 1 := by rw [MonoidHom.inv_apply]; exact inv_ne_one.2 hg₀
  have hN := charSI_isEmpty_iso φ g₀ hg₀
  have hNi := charSI_isEmpty_iso φ⁻¹ g₀ hinv
  have hT := not_NTe_charSI_one (G := G)
  fin_cases e <;> simp [NTe, face6π, face6Label, hN, hNi, hT]

/-- **Exactly six non-trivial links**: the 6-cycle labelling is non-trivial on precisely
the six cycle links. -/
theorem face6π_card (g₀ : G) (hg₀ : φ g₀ ≠ 1) :
    (Finset.univ.filter (NTe (simpleIrr ∘ face6π φ))).card = 6 := by
  have : Finset.univ.filter (NTe (simpleIrr ∘ face6π φ)) = {1, 2, 4, 5, 8, 9} := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact NTe_face6π_iff φ g₀ hg₀ e
  rw [this]
  rfl

/-- **The 6-cycle case is attained on the cube** for every finite group with a non-trivial
character `φ : G →* ℂˣ`. -/
theorem cube_six_cycle_attained (g₀ : G) (hg₀ : φ g₀ ≠ 1) :
    ∃ ψ : (Fin 12 → G) → ℂ, (∀ g, latticeGauge cubeΓ g ψ = ψ) ∧
      ∃ π : Fin 12 → SimpleIdeal G, fourierProj simpleIrr π ψ ≠ 0 ∧
        (Finset.univ.filter (NTe (simpleIrr ∘ π))).card = 6 :=
  ⟨wilson6 φ, wilson6_gauge_invariant φ, face6π φ, fourierProj_wilson6_ne_zero φ,
    face6π_card φ g₀ hg₀⟩

/-- The same, with the short-cycle conclusion of `cube_gauge_support_finite`. -/
theorem cube_six_cycle_attained_shortCycle (g₀ : G) (hg₀ : φ g₀ ≠ 1) :
    ∃ ψ : (Fin 12 → G) → ℂ, (∀ g, latticeGauge cubeΓ g ψ = ψ) ∧
      ∃ π : Fin 12 → SimpleIdeal G, fourierProj simpleIrr π ψ ≠ 0 ∧
        (Finset.univ.filter (NTe (simpleIrr ∘ π))).card = 6 ∧
        shortCycle (supportList cubeΓ (simpleIrr ∘ π) Fin.val) = true := by
  refine ⟨wilson6 φ, wilson6_gauge_invariant φ, face6π φ, fourierProj_wilson6_ne_zero φ,
    face6π_card φ g₀ hg₀, ?_⟩
  exact cube_gauge_support_shortCycle_finite (wilson6 φ) (wilson6_gauge_invariant φ) (face6π φ)
    (fourierProj_wilson6_ne_zero φ) (by rw [face6π_card φ g₀ hg₀]; omega)
    (by rw [face6π_card φ g₀ hg₀])

end WilsonSix

/-! ### `S₃` -/

/-- The sign 6-cycle labelling of `S₃` has exactly 6 non-trivial links. -/
theorem cube_six_card_S3 :
    (Finset.univ.filter (NTe (simpleIrr ∘ face6π signChar))).card = 6 :=
  face6π_card signChar (Equiv.swap 0 1) signChar_swap

/-- **The 6-cycle case is attained on the cube for `S₃`** (sign character on the boundary of
two adjacent faces). -/
theorem cube_six_cycle_attained_S3 :
    ∃ ψ : (Fin 12 → S3) → ℂ, (∀ g, latticeGauge cubeΓ g ψ = ψ) ∧
      ∃ π : Fin 12 → SimpleIdeal S3, fourierProj simpleIrr π ψ ≠ 0 ∧
        (Finset.univ.filter (NTe (simpleIrr ∘ π))).card = 6 :=
  cube_six_cycle_attained signChar (Equiv.swap 0 1) signChar_swap

theorem cube_six_cycle_attained_S3_shortCycle :
    ∃ ψ : (Fin 12 → S3) → ℂ, (∀ g, latticeGauge cubeΓ g ψ = ψ) ∧
      ∃ π : Fin 12 → SimpleIdeal S3, fourierProj simpleIrr π ψ ≠ 0 ∧
        (Finset.univ.filter (NTe (simpleIrr ∘ π))).card = 6 ∧
        shortCycle (supportList cubeΓ (simpleIrr ∘ π) Fin.val) = true :=
  cube_six_cycle_attained_shortCycle signChar (Equiv.swap 0 1) signChar_swap

/-- **Both cases of the cube theorem occur for `S₃`**: for `n = 4` and `n = 6` there is a
nonzero gauge-invariant Fourier component with exactly `n` non-trivial links, on a short
cycle, and (`cube_gauge_support_card_S3`) no other count in `1..6` is possible. -/
theorem cube_four_and_six_attained_S3 (n : ℕ) (hn : n = 4 ∨ n = 6) :
    ∃ ψ : (Fin 12 → S3) → ℂ, (∀ g, latticeGauge cubeΓ g ψ = ψ) ∧
      ∃ π : Fin 12 → SimpleIdeal S3, fourierProj simpleIrr π ψ ≠ 0 ∧
        (Finset.univ.filter (NTe (simpleIrr ∘ π))).card = n ∧
        shortCycle (supportList cubeΓ (simpleIrr ∘ π) Fin.val) = true := by
  rcases hn with rfl | rfl
  · exact cube_four_cycle_attained_S3_shortCycle
  · exact cube_six_cycle_attained_S3_shortCycle

end GaugeSupport

#print axioms GaugeSupport.wilson6_gauge_invariant
#print axioms GaugeSupport.wilson6_mul_labels
#print axioms GaugeSupport.fourierProj_wilson6_ne_zero
#print axioms GaugeSupport.NTe_face6π_iff
#print axioms GaugeSupport.face6π_card
#print axioms GaugeSupport.cube_six_cycle_attained
#print axioms GaugeSupport.cube_six_cycle_attained_shortCycle
#print axioms GaugeSupport.cube_six_card_S3
#print axioms GaugeSupport.cube_six_cycle_attained_S3
#print axioms GaugeSupport.cube_six_cycle_attained_S3_shortCycle
#print axioms GaugeSupport.cube_four_and_six_attained_S3
