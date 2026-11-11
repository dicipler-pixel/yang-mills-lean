-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026 Jeromie Beasley. See LICENSING.md.
import SymWitnessSU3

/-!
# Irreducibility of the sextets `V(2, 0) = Sym²(3)` and `V(0, 2) = Sym²(3̄)`

Author: Jeromie Beasley (Green, Grok Bot), with the Team.
ORCID https://orcid.org/0009-0006-4645-5643 · GitHub dicipler-pixel · X @d1c1pler ·
YouTube @AtlasMemoriae · atlas-memoriae.dicipler.workers.dev

Stacks on #49 (`SymWitnessSU3`), which identifies `V(2, 0)` with the symmetric `3 × 3` matrices
under `S ↦ g S gᵀ` (`psi20`) and `V(0, 2)` with the symmetric matrices under `T ↦ ḡ T ḡᵀ`
(`psi02`, `ḡ = (g*)ᵀ`). Same style as #41 (`IrrepIrreducibleSU3`): explicit SU(3) elements only,
no Lie algebra, no highest-weight theory; simplicity is `CategoryTheory.Simple` in `FDRep ℂ SU3`.

**The matrix argument (`symSub_le_of_stable`).** Let `S ⊆ Sym²` be a subspace stable under
`M ↦ A M Aᵀ` for the five matrices `d₁ = diag(1,-1,-1)`, `d₂ = diag(-1,1,-1)`, the cyclic
permutation, the `3-4-5` rotation and `τ = diag(i, 1, -i)`, and let `0 ≠ M ∈ S`.
* The sign matrices act on the weight lines `E₀₀, E₁₁, E₂₂ | F₀₁ | F₁₂ | F₂₀` (`Fᵢⱼ = Eᵢⱼ + Eⱼᵢ`)
  by the distinct sign characters `(+,+) | (-,-) | (+,-) | (-,+)`, so
  `(M - d₁Md₁) - d₂(M - d₁Md₁)d₂ = 4 M₀₁ F₀₁` isolates `F₀₁` (`F01_mem_of`).
* Some element of `S` has a nonzero `(0,1)` entry (`exists_01_mem`): an off-diagonal entry is
  moved to `(0,1)` by the cyclic permutation; a diagonal `M` with two different diagonal
  entries is moved off the diagonal by the rotation; a scalar `M = a I` (fixed by every real
  rotation, since `R I Rᵀ = I`) is first turned into `diag(-a, a, -a)` by `τ`.
* From `F₀₁`: the rotation gives `E₀₀ - E₁₁`, `τ` gives `-E₀₀ - E₁₁`, hence `E₁₁`, the cyclic
  permutation gives `E₀₀`, and #49's `symSub_le` gives all of `Sym²`.

**Results.**
* `sym_invariant_eq_bot_or_top`: the only SU(3)-stable subspaces of `Sym²(3)` (action
  `S ↦ g S gᵀ`) are `⊥` and `Sym²`.
* `irrep20_invariant_eq_bot_or_top`, **`simple_irrep20`: `V(2, 0)` is simple.**
* `irrep02_invariant_eq_bot_or_top` (directly, with `τ̄ = diag(-i, 1, i)` so that `ḡ = τ`), and
  **`simple_irrep02`: `V(0, 2)` is simple**, through #49's `conj02 : V(0, 2) ≅ V(2, 0)ᘁ` and
  `DualSimple`.

`FalseControls/SymIrreducibleControl.lean` claims the exact negation (some nonzero proper
SU(3)-stable subspace of `V(2, 0)`) and is rejected.

**Not proved (open).** Irreducibility of `V(p, q)` for general `(p, q)`, and the classification
(every irreducible SU(3) representation is some `V(p, q)`).

No continuum or mass-gap statement is made.
-/

open CategoryTheory CentreCharacterSU3 IrrepEmbedSU3 IrrepSmallIsoSU3 IrrepIrreducibleSU3
  SymWitnessSU3

namespace SymIrreducibleSU3

/-! ## Explicit matrices -/

/-- `τ̄ = diag(-i, 1, i)`, the complex conjugate of `τ`; it satisfies `ḡ = τ` for `g = τ̄`. -/
noncomputable def tauBarM : Mat3 := !![-Complex.I, 0, 0; 0, 1, 0; 0, 0, Complex.I]

theorem star_tauBar : star tauBarM = tauM := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [tauBarM, tauM, Matrix.star_apply]

theorem tauBar_mem : tauBarM ∈ SU3 := mem_SU3_of
  (by rw [star_tauBar]; simp [tauM, tauBarM, Matrix.one_fin_three])
  (by simp [tauBarM, Matrix.det_fin_three])

noncomputable def tauBar : SU3 := ⟨tauBarM, tauBar_mem⟩

theorem hb_d1 : hb d1 = d1M := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hb, d1, d1M, Matrix.star_apply]
theorem hb_d2 : hb d2 = d2M := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hb, d2, d2M, Matrix.star_apply]
theorem hb_tauBar : hb tauBar = tauM := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hb, tauBar, tauBarM, tauM, Matrix.star_apply]

/-! ## Entry formulas for `M ↦ A M Aᵀ` -/

theorem cyc_cong_01 (M : Mat3) : (cycMat * M * cycMat.transpose) 0 1 = M 2 0 := by
  rw [cyc_T]; exact cyc_ad_01 M
theorem cyc_cong_10 (M : Mat3) : (cycMat * M * cycMat.transpose) 1 0 = M 0 2 := by
  rw [cyc_T]; exact cyc_ad_10 M
theorem cyc_cong_20 (M : Mat3) : (cycMat * M * cycMat.transpose) 2 0 = M 1 2 := by
  rw [cyc_T]; exact cyc_ad_20 M
theorem cyc_cong_02 (M : Mat3) : (cycMat * M * cycMat.transpose) 0 2 = M 2 1 := by
  rw [cyc_T]; exact cyc_ad_02 M
theorem cyc_cong_00 (M : Mat3) : (cycMat * M * cycMat.transpose) 0 0 = M 2 2 := by
  rw [cyc_T]; exact cyc_ad_00 M
theorem cyc_cong_11 (M : Mat3) : (cycMat * M * cycMat.transpose) 1 1 = M 0 0 := by
  rw [cyc_T]; exact cyc_ad_11 M
theorem cyc_cong_22 (M : Mat3) : (cycMat * M * cycMat.transpose) 2 2 = M 1 1 := by
  rw [cyc_T]; exact cyc_ad_22 M
theorem rot_cong_01 (M : Mat3) :
    (rotM * M * rotM.transpose) 0 1 = (12 * M 0 0 + 9 * M 0 1 - 16 * M 1 0 - 12 * M 1 1) / 25 := by
  rw [rot_T]; exact rot_ad_01 M

theorem tau_cong_00 (M : Mat3) : (tauM * M * tauM.transpose) 0 0 = -M 0 0 := by
  rw [Matrix.eta_fin_three M]
  simp [tauM, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]
  linear_combination (M 0 0) * Complex.I_mul_I
theorem tau_cong_11 (M : Mat3) : (tauM * M * tauM.transpose) 1 1 = M 1 1 := by
  rw [Matrix.eta_fin_three M]
  simp [tauM, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]
theorem tau_cong_01 (M : Mat3) : (tauM * M * tauM.transpose) 0 1 = Complex.I * M 0 1 := by
  rw [Matrix.eta_fin_three M]
  simp [tauM, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]
theorem tau_cong_10 (M : Mat3) : (tauM * M * tauM.transpose) 1 0 = Complex.I * M 1 0 := by
  rw [Matrix.eta_fin_three M]
  simp [tauM, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]
  ring

theorem d1_T : d1M.transpose = d1M := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [d1M]
theorem d2_T : d2M.transpose = d2M := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [d2M]

/-- **The sign matrices isolate the `(0,1)` weight line:**
`(M - d₁Md₁ᵀ) - d₂(M - d₁Md₁ᵀ)d₂ᵀ = 4 M₀₁ E₀₁ + 4 M₁₀ E₁₀`. -/
theorem signs_proj01 (M : Mat3) :
    (M - d1M * M * d1M.transpose) - d2M * (M - d1M * M * d1M.transpose) * d2M.transpose =
      (4 * M 0 1) • E 0 1 + (4 * M 1 0) • E 1 0 := by
  rw [d1_T, d2_T, Matrix.eta_fin_three M]
  ext i j; fin_cases i <;> fin_cases j <;> simp [d1M, d2M] <;> ring

/-- `E₀₀ - E₁₁` from the rotated `F₀₁`: `R F₀₁ Rᵀ = -(24/25)(E₀₀ - E₁₁) - (7/25) F₀₁`. -/
theorem rot_F01_diag :
    E 0 0 - E 1 1 = (-(25/24) : ℂ) • (rotM * F 0 1 * rotM.transpose + (7/25 : ℂ) • F 0 1) := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.smul_apply,
      Matrix.add_apply, Matrix.sub_apply] <;>
    simp [rotM] <;> norm_num

/-- `E₁₁ = -½ ((E₀₀ - E₁₁) + τ (E₀₀ - E₁₁) τᵀ)`, since `τ E₀₀ τᵀ = -E₀₀`. -/
theorem tau_diag_E11 :
    E 1 1 = (-(1/2) : ℂ) • ((E 0 0 - E 1 1) + tauM * (E 0 0 - E 1 1) * tauM.transpose) := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.smul_apply,
      Matrix.add_apply, Matrix.sub_apply] <;>
    (simp [tauM]; try norm_num)

/-! ## Stable subspaces of `Sym²` -/

/-- `S` is stable under the congruence `M ↦ A M Aᵀ`. -/
def CongStable (S : Submodule ℂ Mat3) (A : Mat3) : Prop := ∀ M ∈ S, A * M * A.transpose ∈ S

section
variable {S : Submodule ℂ Mat3} (hsym : S ≤ symSub) (hd1 : CongStable S d1M)
  (hd2 : CongStable S d2M) (hc : CongStable S cycMat) (hr : CongStable S rotM)
  (ht : CongStable S tauM)

include hsym hd1 hd2 in
/-- A symmetric element with nonzero `(0,1)` entry puts `F₀₁` in `S`. -/
theorem F01_mem_of {M : Mat3} (hM : M ∈ S) (h : M 0 1 ≠ 0) : F 0 1 ∈ S := by
  have hMs : M.transpose = M := hsym hM
  have h10 : M 1 0 = M 0 1 := by have := congrFun (congrFun hMs 0) 1; simpa using this
  have h1 : M - d1M * M * d1M.transpose ∈ S := S.sub_mem hM (hd1 M hM)
  have h2 := S.sub_mem h1 (hd2 _ h1)
  rw [signs_proj01, h10, ← smul_add] at h2
  have h4 : (4 * M 0 1) ≠ 0 := mul_ne_zero (by norm_num) h
  have := S.smul_mem (4 * M 0 1)⁻¹ h2
  rwa [smul_smul, inv_mul_cancel₀ h4, one_smul] at this

include hsym hc hr ht in
/-- **A nonzero element of `S` yields one with a nonzero `(0,1)` entry.** -/
theorem exists_01_mem {M : Mat3} (hM : M ∈ S) (hM0 : M ≠ 0) : ∃ N ∈ S, N 0 1 ≠ 0 := by
  have hMs : M.transpose = M := hsym hM
  have h10 : M 1 0 = M 0 1 := by have := congrFun (congrFun hMs 0) 1; simpa using this
  have h21 : M 2 1 = M 1 2 := by have := congrFun (congrFun hMs 1) 2; simpa using this
  have h02 : M 0 2 = M 2 0 := by have := congrFun (congrFun hMs 2) 0; simpa using this
  have c1 := hc M hM
  have c2 := hc _ c1
  by_cases a01 : M 0 1 ≠ 0
  · exact ⟨M, hM, a01⟩
  by_cases a20 : M 2 0 ≠ 0
  · exact ⟨_, c1, by rw [cyc_cong_01]; exact a20⟩
  by_cases a12 : M 1 2 ≠ 0
  · exact ⟨_, c2, by rw [cyc_cong_01, cyc_cong_20]; exact a12⟩
  push Not at a01 a20 a12
  by_cases ha : M 0 0 ≠ M 1 1
  · refine ⟨_, hr M hM, ?_⟩
    rw [rot_cong_01, a01, h10, a01]
    intro h0
    apply ha
    linear_combination (25 / 12 : ℂ) * h0
  by_cases hb' : M 1 1 ≠ M 2 2
  · refine ⟨_, hr _ c2, ?_⟩
    rw [rot_cong_01, cyc_cong_00, cyc_cong_01, cyc_cong_10, cyc_cong_22, cyc_cong_20,
      cyc_cong_02, cyc_cong_11, cyc_cong_00, a12, h21, a12]
    intro h0
    apply hb'
    linear_combination (25 / 12 : ℂ) * h0
  push Not at ha hb'
  have h00 : M 0 0 ≠ 0 := by
    intro h0
    apply hM0
    have h1 : M 1 1 = 0 := by rw [← ha, h0]
    have h2 : M 2 2 = 0 := by rw [← hb', h1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h0, h1, h2, a01, h10, a12, h21, a20, h02]
  refine ⟨_, hr _ (ht M hM), ?_⟩
  rw [rot_cong_01, tau_cong_00, tau_cong_01, tau_cong_10, tau_cong_11, a01, h10, a01, ← ha]
  intro h0
  apply h00
  linear_combination (-(25 / 24) : ℂ) * h0

include hsym hd1 hd2 hc hr ht in
/-- **A subspace of `Sym²` stable under the five explicit congruences and containing a nonzero
matrix is all of `Sym²`.** -/
theorem symSub_le_of_stable {M : Mat3} (hM : M ∈ S) (hM0 : M ≠ 0) : symSub ≤ S := by
  obtain ⟨N, hN, hN01⟩ := exists_01_mem hsym hc hr ht hM hM0
  have f01 := F01_mem_of hsym hd1 hd2 hN hN01
  have dd : E 0 0 - E 1 1 ∈ S := by
    rw [rot_F01_diag]
    exact S.smul_mem _ (S.add_mem (hr _ f01) (S.smul_mem _ f01))
  have e11 : E 1 1 ∈ S := by
    rw [tau_diag_E11]
    exact S.smul_mem _ (S.add_mem dd (ht _ dd))
  have e22 : E 2 2 ∈ S := by have := hc _ e11; rw [cyc_conjT] at this; simpa using this
  have e00 : E 0 0 ∈ S := by have := hc _ e22; rw [cyc_conjT] at this; simpa using this
  exact symSub_le S hc hr e00

end

/-- **`Sym²(3)` is irreducible:** the only subspaces of the symmetric matrices stable under
`S ↦ g S gᵀ` for every `g ∈ SU(3)` are `⊥` and `Sym²`. -/
theorem sym_invariant_eq_bot_or_top (S : Submodule ℂ Mat3) (hsym : S ≤ symSub)
    (hS : ∀ g : SU3, ∀ M ∈ S, g.1 * M * g.1.transpose ∈ S) : S = ⊥ ∨ S = symSub := by
  by_cases h : S = ⊥
  · exact Or.inl h
  right
  obtain ⟨M, hM, hM0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  exact le_antisymm hsym (symSub_le_of_stable hsym (hS d1) (hS d2) (hS cyc) (hS rot) (hS tau)
    hM hM0)

/-! ## `V(2, 0)` and `V(0, 2)` are simple -/

/-- **The only SU(3)-stable subspaces of `V(2, 0)` are `⊥` and `⊤`.** -/
theorem irrep20_invariant_eq_bot_or_top (W : Submodule ℂ (irrepRep 2 0))
    (hW : ∀ g, ∀ w ∈ W, (irrepRep 2 0).ρ g w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases h : W = ⊥
  · exact Or.inl h
  right
  let S : Submodule ℂ Mat3 := W.map psi20
  have hsym : S ≤ symSub := by
    rintro _ ⟨w, -, rfl⟩
    exact psi20_mem w
  have hS : ∀ g : SU3, CongStable S g.1 := by
    rintro g _ ⟨w, hw, rfl⟩
    exact ⟨(irrepRep 2 0).ρ g w, hW g w hw, psi20_rho g w⟩
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  have hfw : psi20 w ≠ 0 := fun h0 => hw0 (psi20_injective (h0.trans (map_zero psi20).symm))
  have hle := symSub_le_of_stable hsym (hS d1) (hS d2) (hS cyc) (hS rot) (hS tau)
    (⟨w, hw, rfl⟩ : psi20 w ∈ S) hfw
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hyx⟩ := hle (psi20_mem x)
  rw [← psi20_injective hyx]
  exact hy

/-- **`V(2, 0) = Sym²(3)`, the sextet, is simple.** -/
theorem simple_irrep20 : Simple (irrepRep 2 0) :=
  simple_of_invariant _ ⟨⟨hwIrrep 2 0, 0, hwIrrep_ne_zero 2 0⟩⟩ irrep20_invariant_eq_bot_or_top

/-- **The only SU(3)-stable subspaces of `V(0, 2)` are `⊥` and `⊤`** (directly, through
`T ↦ ḡ T ḡᵀ`; for `d₁, d₂`, the cyclic permutation and the rotation `ḡ = g`, and `τ̄` gives
`ḡ = τ`). -/
theorem irrep02_invariant_eq_bot_or_top (W : Submodule ℂ (irrepRep 0 2))
    (hW : ∀ g, ∀ w ∈ W, (irrepRep 0 2).ρ g w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases h : W = ⊥
  · exact Or.inl h
  right
  let S : Submodule ℂ Mat3 := W.map psi02
  have hsym : S ≤ symSub := by
    rintro _ ⟨w, -, rfl⟩
    exact psi02_mem w
  have hS : ∀ g : SU3, CongStable S (hb g) := by
    rintro g _ ⟨w, hw, rfl⟩
    exact ⟨(irrepRep 0 2).ρ g w, hW g w hw, psi02_rho g w⟩
  have s1 := hS d1
  have s2 := hS d2
  have sc := hS cyc
  have sr := hS rot
  have st := hS tauBar
  rw [hb_d1] at s1
  rw [hb_d2] at s2
  rw [hb_cyc] at sc
  rw [hb_rot] at sr
  rw [hb_tauBar] at st
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  have hfw : psi02 w ≠ 0 := fun h0 => hw0 (psi02_injective (h0.trans (map_zero psi02).symm))
  have hle := symSub_le_of_stable hsym s1 s2 sc sr st (⟨w, hw, rfl⟩ : psi02 w ∈ S) hfw
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hyx⟩ := hle (psi02_mem x)
  rw [← psi02_injective hyx]
  exact hy

/-- `V(0, 2)` is simple, directly from its stable subspaces. -/
theorem simple_irrep02_direct : Simple (irrepRep 0 2) :=
  simple_of_invariant _ ⟨⟨hwIrrep 0 2, 0, hwIrrep_ne_zero 0 2⟩⟩ irrep02_invariant_eq_bot_or_top

/-- **`V(0, 2) = Sym²(3̄)`, the antisextet, is simple**, through #49's
`conj02 : V(0, 2) ≅ V(2, 0)ᘁ` and the simplicity of duals (`DualSimple`). -/
theorem simple_irrep02 : Simple (irrepRep 0 2) :=
  haveI := simple_irrep20
  haveI := GaugeSupport.dual_simple (irrepRep 2 0)
  Simple.of_iso conj02

/-- **Both sextets are simple.** -/
theorem simple_irrep20_and_02 : Simple (irrepRep 2 0) ∧ Simple (irrepRep 0 2) :=
  ⟨simple_irrep20, simple_irrep02⟩

end SymIrreducibleSU3
