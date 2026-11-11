import IrrepSmallIsoSU3

/-!
# Irreducibility of `V(1, 0)`, `V(0, 1)`, `V(0, 0)` and `V(1, 1)`; `V(1, 1)` is the traceless part of `3 ⊗ 3̄`

Author: Jeromie Beasley (Spectrum · Colour team lead, Grok Bot), with the Team.
ORCID https://orcid.org/0009-0006-4645-5643 · GitHub dicipler-pixel · X @d1c1pler ·
YouTube @AtlasMemoriae · atlas-memoriae.dicipler.workers.dev

Irreducibility in the first concrete cases, by explicit group elements of SU(3) (no Lie algebra,
no highest-weight theory). Simplicity is `CategoryTheory.Simple` in `FDRep ℂ SU3`, the notion
used by `DualSimple` and by Grey's finite Peter–Weyl file.

**From subspaces to `Simple`.** `simple_of_invariant` : a nonzero `X : FDRep ℂ SU3` whose only
SU(3)-stable subspaces are `⊥` and `⊤` is `Simple` (the range of a nonzero mono is stable, so
it is `⊤` and the mono is bijective).

**`3` is simple.** `fund_invariant_eq_bot_or_top`: a nonzero stable `W ⊆ ℂ³` contains a vector
with nonzero first coordinate (rotate by `cyc`), then `v + d₁ v = 2 v₀ e₀` with the sign
matrix `d₁ = diag(1, -1, -1) ∈ SU(3)`, so `e₀ ∈ W`, and `cyc` reaches `e₁`, `e₂`. Hence
`simple_fund`; `simple_antifund` from `DualSimple.dual_simple`; `simple_unit` (`𝟙`);
and through the isos of `IrrepSmallIsoSU3`, `simple_irrep10`, `simple_irrep01`,
`simple_irrep00`.

**`V(1, 1)` = traceless part of `3 ⊗ 3̄`.** `phi11 : 3 ⊗ (3̄ ⊗ 𝟙) → M₃(ℂ)`,
`x ⊗ (φ ⊗ c) ↦ c (xᵢ φ(eⱼ))ᵢⱼ`, is a linear bijection (`phiT_bijective`) and SU(3)-equivariant
for the adjoint action `M ↦ g M g⁻¹` (`phi11_equivariant`). It sends the highest-weight vector
`e₁ ⊗ e₃* ⊗ 1` to the matrix unit `E₀₂` (`phi11_hw`). Composing with the trace gives the
contraction `contract11 (x ⊗ (φ ⊗ c)) = c φ(x)` (`contract11_tmul`).
* `traceless_le_of_adInvariant`: an Ad-invariant subspace of `M₃(ℂ)` containing a nonzero
  traceless matrix contains every traceless matrix. Sign matrices `diag(1,-1,-1)`,
  `diag(-1,1,-1)` and `τ = diag(i, 1, -i)` isolate an off-diagonal entry (`single01_mem_of`);
  `cyc` and the signed swap move it to `(0, 1)` (`exists_01_of`); a diagonal traceless matrix
  is first moved off the diagonal by the rotation `rot` with entries `3/5, 4/5`
  (`exists_01_mem`); from `E₀₁` the same elements produce all six `Eᵢⱼ` and `E₀₀ - E₁₁`,
  `E₁₁ - E₂₂`.
* `irrepSub11_map_eq`: `Φ(V(1,1)) = sl₃ = {trace = 0}`; `irrepSub11_eq_ker_contract`:
  `V(1, 1) = ker contract11`, the kernel of the evaluation pairing `3 ⊗ 3̄ → ℂ`.
* `finrank_tracelessSub`, `finrank_irrepSub11`, `finrank_irrepRep11`: dimension `8`;
  `finrank_tensorRep11`: the ambient `3 ⊗ 3̄ ⊗ 𝟙` has dimension `9`;
  `irrep11_finrank_ne_nine`.
* `irrep11_invariant_eq_bot_or_top` and `simple_irrep11`: **`V(1, 1)` is simple.**

`FalseControls/Irrep11DimControl.lean` claims `finrank V(1, 1) = 9` and is rejected.

**Not proved (open).** Irreducibility of `V(p, q)` for general `(p, q)`, and the
classification (every irreducible SU(3) representation is some `V(p, q)`).

No continuum or mass-gap statement is made.
-/

open CategoryTheory MonoidalCategory CentreCharacterSU3 IrrepEmbedSU3 IrrepSmallIsoSU3
  SingletWitnessSU3

namespace IrrepIrreducibleSU3

abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℂ

/-- Membership in SU(3) for an explicit matrix. -/
theorem mem_SU3_of {G : Mat3} (hu : star G * G = 1) (hd : G.det = 1) : G ∈ SU3 := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff']
  exact ⟨hu, hd⟩

noncomputable def d1M : Mat3 := !![1, 0, 0; 0, -1, 0; 0, 0, -1]
noncomputable def d2M : Mat3 := !![-1, 0, 0; 0, 1, 0; 0, 0, -1]
noncomputable def tauM : Mat3 := !![Complex.I, 0, 0; 0, 1, 0; 0, 0, -Complex.I]
noncomputable def swapM : Mat3 := !![0, 1, 0; 1, 0, 0; 0, 0, -1]
noncomputable def rotM : Mat3 := !![3/5, -4/5, 0; 4/5, 3/5, 0; 0, 0, 1]

theorem star_d1 : star d1M = d1M := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [d1M, Matrix.star_apply]
theorem star_d2 : star d2M = d2M := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [d2M, Matrix.star_apply]
theorem star_tau : star tauM = !![-Complex.I, 0, 0; 0, 1, 0; 0, 0, Complex.I] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [tauM, Matrix.star_apply]
theorem star_swap : star swapM = swapM := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [swapM, Matrix.star_apply]
theorem star_rot : star rotM = !![3/5, 4/5, 0; -4/5, 3/5, 0; 0, 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotM, Matrix.star_apply]
theorem star_cyc : star cycMat = !![0, 1, 0; 0, 0, 1; 1, 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cycMat, Matrix.star_apply]

theorem d1_mem : d1M ∈ SU3 := mem_SU3_of (by rw [star_d1]; simp [d1M, Matrix.one_fin_three])
  (by simp [d1M, Matrix.det_fin_three])
theorem d2_mem : d2M ∈ SU3 := mem_SU3_of (by rw [star_d2]; simp [d2M, Matrix.one_fin_three])
  (by simp [d2M, Matrix.det_fin_three])
theorem tau_mem : tauM ∈ SU3 := mem_SU3_of (by rw [star_tau]; simp [tauM, Matrix.one_fin_three])
  (by simp [tauM, Matrix.det_fin_three])
theorem swap_mem : swapM ∈ SU3 := mem_SU3_of (by rw [star_swap]; simp [swapM, Matrix.one_fin_three])
  (by simp [swapM, Matrix.det_fin_three])
theorem rot_mem : rotM ∈ SU3 := mem_SU3_of
  (by rw [star_rot]; simp [rotM, Matrix.one_fin_three]; norm_num)
  (by simp [rotM, Matrix.det_fin_three]; norm_num)

noncomputable def d1 : SU3 := ⟨d1M, d1_mem⟩
noncomputable def d2 : SU3 := ⟨d2M, d2_mem⟩
noncomputable def tau : SU3 := ⟨tauM, tau_mem⟩
noncomputable def swap : SU3 := ⟨swapM, swap_mem⟩
noncomputable def rot : SU3 := ⟨rotM, rot_mem⟩

/-- The adjoint action `M ↦ g M g⁻¹` of SU(3) on 3×3 matrices. -/
def AdInvariant (S : Submodule ℂ Mat3) : Prop := ∀ g : SU3, ∀ M ∈ S, g.1 * M * star g.1 ∈ S

/-- The matrix unit `E i j`. -/
noncomputable abbrev E (i j : Fin 3) : Mat3 := Matrix.single i j 1

/-- `cyc M cyc⁻¹` has entries `M (a-1) (b-1)`; the two we use. -/
theorem cyc_ad_01 (M : Mat3) : (cycMat * M * star cycMat) 0 1 = M 2 0 := by
  rw [star_cyc, Matrix.eta_fin_three M]; simp [cycMat]
theorem cyc_ad_10 (M : Mat3) : (cycMat * M * star cycMat) 1 0 = M 0 2 := by
  rw [star_cyc, Matrix.eta_fin_three M]; simp [cycMat]
theorem cyc_ad_20 (M : Mat3) : (cycMat * M * star cycMat) 2 0 = M 1 2 := by
  rw [star_cyc, Matrix.eta_fin_three M]; simp [cycMat]
theorem cyc_ad_02 (M : Mat3) : (cycMat * M * star cycMat) 0 2 = M 2 1 := by
  rw [star_cyc, Matrix.eta_fin_three M]; simp [cycMat]
theorem cyc_ad_00 (M : Mat3) : (cycMat * M * star cycMat) 0 0 = M 2 2 := by
  rw [star_cyc, Matrix.eta_fin_three M]; simp [cycMat]
theorem cyc_ad_11 (M : Mat3) : (cycMat * M * star cycMat) 1 1 = M 0 0 := by
  rw [star_cyc, Matrix.eta_fin_three M]; simp [cycMat]
theorem cyc_ad_22 (M : Mat3) : (cycMat * M * star cycMat) 2 2 = M 1 1 := by
  rw [star_cyc, Matrix.eta_fin_three M]; simp [cycMat]
theorem rot_ad_01 (M : Mat3) :
    (rotM * M * star rotM) 0 1 = (12 * M 0 0 + 9 * M 0 1 - 16 * M 1 0 - 12 * M 1 1) / 25 := by
  rw [star_rot, Matrix.eta_fin_three M]; simp [rotM]; ring
theorem swap_ad_01 (M : Mat3) : (swapM * M * star swapM) 0 1 = M 1 0 := by
  rw [star_swap, Matrix.eta_fin_three M]; simp [swapM]

theorem cyc_ad_single (i j : Fin 3) :
    cycMat * E i j * star cycMat = E (i + 1) (j + 1) := by
  rw [star_cyc]
  fin_cases i <;> fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_three] <;> simp [cycMat]

theorem swap_ad_single01 : swapM * E 0 1 * star swapM = E 1 0 := by
  rw [star_swap]
  ext a b; fin_cases a <;> fin_cases b <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_three] <;> simp [swapM]

/-- The rotation in the `(0,1)` plane turns `E 0 1` into a matrix with diagonal part
`-(12/25)(E 0 0 - E 1 1)`. -/
theorem rot_ad_single01 :
    rotM * E 0 1 * star rotM =
      (9/25 : ℂ) • E 0 1 - (16/25 : ℂ) • E 1 0 - (12/25 : ℂ) • (E 0 0 - E 1 1) := by
  rw [star_rot]
  ext a b; fin_cases a <;> fin_cases b <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_three] <;> simp [rotM] <;> norm_num

/-- The traceless 3×3 matrices, the kernel of the trace. -/
noncomputable def tracelessSub : Submodule ℂ Mat3 :=
  LinearMap.ker (Matrix.traceLinearMap (Fin 3) ℂ ℂ)

theorem mem_tracelessSub {X : Mat3} : X ∈ tracelessSub ↔ X.trace = 0 := Iff.rfl

section
variable {S : Submodule ℂ Mat3} (hS : AdInvariant S)
include hS

theorem ad_mem {G : Mat3} (hG : G ∈ SU3) {M : Mat3} (hM : M ∈ S) : G * M * star G ∈ S :=
  hS ⟨G, hG⟩ M hM

/-- Isolating the `(0,1)` entry with sign matrices and `τ`. -/
theorem single01_mem_of {M : Mat3} (hM : M ∈ S) (h : M 0 1 ≠ 0) : E 0 1 ∈ S := by
  set X1 := M - d1M * M * star d1M
  set X2 := X1 - d2M * X1 * star d2M
  set X3 := X2 - Complex.I • (tauM * X2 * star tauM)
  have h1 : X1 ∈ S := sub_mem hM (ad_mem hS d1_mem hM)
  have h2 : X2 ∈ S := sub_mem h1 (ad_mem hS d2_mem h1)
  have h3 : X3 ∈ S := sub_mem h2 (S.smul_mem _ (ad_mem hS tau_mem h2))
  have hX : X3 = (8 * M 0 1) • E 0 1 := by
    simp only [X3, X2, X1, star_d1, star_d2, star_tau]
    rw [Matrix.eta_fin_three M]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [d1M, d2M, tauM] <;> ring_nf
    all_goals simp [Complex.I_sq]
    all_goals ring_nf
  have h8 : (8 * M 0 1) ≠ 0 := mul_ne_zero (by norm_num) h
  have := S.smul_mem (8 * M 0 1)⁻¹ h3
  rwa [hX, smul_smul, inv_mul_cancel₀ h8, one_smul] at this


/-- A nonzero off-diagonal entry can be moved to position `(0,1)`. -/
theorem exists_01_of {M : Mat3} (hM : M ∈ S) {i j : Fin 3} (hij : i ≠ j) (h : M i j ≠ 0) :
    ∃ N ∈ S, N 0 1 ≠ 0 := by
  have c1 := ad_mem hS cyc_mem hM
  have c2 := ad_mem hS cyc_mem c1
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact ⟨M, hM, h⟩
  · exact ⟨_, ad_mem hS swap_mem c1, by rw [swap_ad_01, cyc_ad_10]; exact h⟩
  · exact ⟨_, ad_mem hS swap_mem hM, by rw [swap_ad_01]; exact h⟩
  · exact absurd rfl hij
  · exact ⟨_, c2, by rw [cyc_ad_01, cyc_ad_20]; exact h⟩
  · exact ⟨_, c1, by rw [cyc_ad_01]; exact h⟩
  · exact ⟨_, ad_mem hS swap_mem c2, by rw [swap_ad_01, cyc_ad_10, cyc_ad_02]; exact h⟩
  · exact absurd rfl hij


/-- A nonzero traceless matrix in an Ad-invariant subspace yields one with a nonzero
`(0,1)` entry. -/
theorem exists_01_mem {M : Mat3} (hM : M ∈ S) (hM0 : M ≠ 0) (htr : M.trace = 0) :
    ∃ N ∈ S, N 0 1 ≠ 0 := by
  by_cases hoff : ∃ i j : Fin 3, i ≠ j ∧ M i j ≠ 0
  · obtain ⟨i, j, hij, h⟩ := hoff
    exact exists_01_of hS hM hij h
  push Not at hoff
  have h01 := hoff 0 1 (by decide)
  have h10 := hoff 1 0 (by decide)
  have h12 := hoff 1 2 (by decide)
  have h21 := hoff 2 1 (by decide)
  by_cases ha : M 0 0 ≠ M 1 1
  · refine ⟨_, ad_mem hS rot_mem hM, ?_⟩
    rw [rot_ad_01, h01, h10]
    intro h0
    apply ha
    linear_combination (25 / 12 : ℂ) * h0
  by_cases hb : M 1 1 ≠ M 2 2
  · have c2 := ad_mem hS cyc_mem (ad_mem hS cyc_mem hM)
    refine ⟨_, ad_mem hS rot_mem c2, ?_⟩
    rw [rot_ad_01, cyc_ad_00, cyc_ad_01, cyc_ad_10, cyc_ad_22, cyc_ad_20, cyc_ad_02,
      cyc_ad_11, cyc_ad_00, h12, h21]
    intro h0
    apply hb
    linear_combination (25 / 12 : ℂ) * h0
  push Not at ha hb
  exfalso
  apply hM0
  have htr' : M 0 0 + M 1 1 + M 2 2 = 0 := by
    rw [← htr]; simp [Matrix.trace, Fin.sum_univ_three]
  have h0 : M 0 0 = 0 := by linear_combination (htr' + 2 * ha + hb) / 3
  have h1 : M 1 1 = 0 := by rw [← ha, h0]
  have h2 : M 2 2 = 0 := by rw [← hb, h1]
  have h02 := hoff 0 2 (by decide)
  have h20 := hoff 2 0 (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h0, h1, h2, h01, h10, h12, h21, h02, h20]

/-- **Every traceless matrix lies in a nonzero Ad-invariant subspace containing a nonzero
traceless matrix.** -/
theorem traceless_le_of_adInvariant {M : Mat3} (hM : M ∈ S) (hM0 : M ≠ 0)
    (htr : M.trace = 0) : tracelessSub ≤ S := by
  obtain ⟨N, hN, hN01⟩ := exists_01_mem hS hM hM0 htr
  have e01 := single01_mem_of hS hN hN01
  have e12 : E 1 2 ∈ S := by
    have := ad_mem hS cyc_mem e01; rwa [cyc_ad_single] at this
  have e20 : E 2 0 ∈ S := by
    have := ad_mem hS cyc_mem e12; rwa [cyc_ad_single] at this
  have e10 : E 1 0 ∈ S := by
    have := ad_mem hS swap_mem e01; rwa [swap_ad_single01] at this
  have e21 : E 2 1 ∈ S := by
    have := ad_mem hS cyc_mem e10; rwa [cyc_ad_single] at this
  have e02 : E 0 2 ∈ S := by
    have := ad_mem hS cyc_mem e21; rwa [cyc_ad_single] at this
  have d01 : E 0 0 - E 1 1 ∈ S := by
    have hr := ad_mem hS rot_mem e01
    rw [rot_ad_single01] at hr
    have : E 0 0 - E 1 1 = (-(25/12 : ℂ)) •
        (((9/25 : ℂ) • E 0 1 - (16/25 : ℂ) • E 1 0 - (12/25 : ℂ) • (E 0 0 - E 1 1)) -
          (9/25 : ℂ) • E 0 1 + (16/25 : ℂ) • E 1 0) := by
      rw [show ((9/25 : ℂ) • E 0 1 - (16/25 : ℂ) • E 1 0 - (12/25 : ℂ) • (E 0 0 - E 1 1)) -
          (9/25 : ℂ) • E 0 1 + (16/25 : ℂ) • E 1 0 = (-(12/25 : ℂ)) • (E 0 0 - E 1 1) by
        module, smul_smul]
      norm_num
    rw [this]
    exact S.smul_mem _ (add_mem (sub_mem hr (S.smul_mem _ e01)) (S.smul_mem _ e10))
  have d12 : E 1 1 - E 2 2 ∈ S := by
    have := ad_mem hS cyc_mem d01
    rwa [Matrix.mul_sub, Matrix.sub_mul, cyc_ad_single, cyc_ad_single] at this
  intro X hX
  have htr : X 0 0 + X 1 1 + X 2 2 = 0 := by
    have : X.trace = 0 := hX
    rw [← this]; simp [Matrix.trace, Fin.sum_univ_three]
  have hdec : X = X 0 1 • E 0 1 + X 0 2 • E 0 2 + X 1 0 • E 1 0 + X 1 2 • E 1 2 +
      X 2 0 • E 2 0 + X 2 1 • E 2 1 + X 0 0 • (E 0 0 - E 1 1) +
      (X 0 0 + X 1 1) • (E 1 1 - E 2 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    linear_combination htr
  rw [hdec]
  refine add_mem (add_mem (add_mem (add_mem (add_mem (add_mem (add_mem ?_ ?_) ?_) ?_) ?_) ?_)
    ?_) ?_ <;> exact S.smul_mem _ ‹_›

end

/-- **The traceless subspace is 8-dimensional.** -/
theorem finrank_tracelessSub : Module.finrank ℂ tracelessSub = 8 := by
  have hsurj : LinearMap.range (Matrix.traceLinearMap (Fin 3) ℂ ℂ) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    refine ⟨c • E 0 0, ?_⟩
    simp [Matrix.trace]
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.traceLinearMap (Fin 3) ℂ ℂ)
  rw [hsurj, finrank_top, Module.finrank_self, Module.finrank_matrix, Fintype.card_fin] at h
  change Module.finrank ℂ (LinearMap.ker (Matrix.traceLinearMap (Fin 3) ℂ ℂ)) = 8
  rw [Module.finrank_self] at h
  omega


/-! ## The map `Φ : 3 ⊗ (3̄ ⊗ 𝟙) → M₃(ℂ)` -/


noncomputable def pairMat : fund →ₗ[ℂ] antifund →ₗ[ℂ] Mat3 :=
  LinearMap.mk₂ ℂ (fun x φ => Matrix.of fun i j =>
      (show Fin 3 → ℂ from x) i * (show Module.Dual ℂ (Fin 3 → ℂ) from φ) (Pi.single j 1))
    (fun x y φ => by ext i j; exact add_mul _ _ _)
    (fun c x φ => by ext i j; exact mul_assoc _ _ _)
    (fun x φ ψ => by ext i j; exact mul_add _ _ _)
    (fun c x φ => by ext i j; exact mul_left_comm _ _ _)

/-- The underlying space of `3 ⊗ (3̄ ⊗ 𝟙)`. -/
abbrev T11 := TensorProduct ℂ fund (TensorProduct ℂ antifund ℂ)

/-- `Φ : 3 ⊗ (3̄ ⊗ 𝟙) → M₃(ℂ)`, `x ⊗ (φ ⊗ c) ↦ c · (xᵢ φ(eⱼ))ᵢⱼ`. -/
noncomputable def phiT : T11 →ₗ[ℂ] Mat3 :=
  TensorProduct.lift pairMat ∘ₗ
    TensorProduct.map LinearMap.id (TensorProduct.rid ℂ antifund).toLinearMap

theorem phiT_tmul (x : fund) (φ : antifund) (c : ℂ) :
    phiT (x ⊗ₜ[ℂ] (φ ⊗ₜ[ℂ] c)) = c • pairMat x φ := by
  simp only [phiT, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearEquiv.coe_toLinearMap, TensorProduct.rid_tmul, TensorProduct.lift.tmul, map_smul]

theorem pairMat_apply (x : fund) (φ : antifund) (i j : Fin 3) :
    pairMat x φ i j =
      (show Fin 3 → ℂ from x) i * (show Module.Dual ℂ (Fin 3 → ℂ) from φ) (Pi.single j 1) := rfl

/-- A linear functional on `ℂ³` in coordinates. -/
theorem dual_expand (φ : Module.Dual ℂ (Fin 3 → ℂ)) (v : Fin 3 → ℂ) :
    φ v = ∑ l, v l * φ (Pi.single l 1) := by
  conv_lhs => rw [show v = ∑ l, v l • (Pi.single l 1 : Fin 3 → ℂ) by
    ext k; simp [Finset.sum_apply, Pi.single_apply]]
  simp [map_sum, map_smul]

theorem pairMat_equivariant (g : SU3) (x : fund) (φ : antifund) :
    pairMat (fund.ρ g x) (antifund.ρ g φ) = g.1 * pairMat x φ * star g.1 := by
  ext i j
  rw [pairMat_apply]
  have hφ : (show Module.Dual ℂ (Fin 3 → ℂ) from antifund.ρ g φ) (Pi.single j 1) =
      (show Module.Dual ℂ (Fin 3 → ℂ) from φ) (fund.ρ g⁻¹ (Pi.single j 1)) :=
    GaugeSupport.dual_ρ_apply fund g φ _
  rw [hφ]
  change (Matrix.mulVec g.1 (show Fin 3 → ℂ from x)) i *
    (show Module.Dual ℂ (Fin 3 → ℂ) from φ) (Matrix.mulVec (star g.1) (Pi.single j 1)) = _
  rw [dual_expand _ (Matrix.mulVec (star g.1) (Pi.single j 1))]
  simp only [Matrix.mul_apply, Fin.sum_univ_three, pairMat_apply, Matrix.mulVec,
    dotProduct, Pi.single_apply]
  fin_cases j <;> simp <;> ring

theorem phiT_equivariant (g : SU3) (t : T11) :
    phiT (TensorProduct.map (fund.ρ g) (TensorProduct.map (antifund.ρ g) LinearMap.id) t) =
      g.1 * phiT t * star g.1 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, Matrix.mul_add, Matrix.add_mul]
  | tmul x y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb =>
      rw [TensorProduct.tmul_add, map_add, map_add, ha, hb, map_add, Matrix.mul_add,
        Matrix.add_mul]
    | tmul φ c =>
      rw [TensorProduct.map_tmul, TensorProduct.map_tmul, LinearMap.id_apply, phiT_tmul,
        phiT_tmul, pairMat_equivariant, Matrix.mul_smul, Matrix.smul_mul]

/-- `Φ` on `tensorRep 1 1`. -/
noncomputable def phi11 : tensorRep 1 1 →ₗ[ℂ] Mat3 := phiT

/-- **`Φ` is SU(3)-equivariant:** `Φ (g · t) = g Φ(t) g⁻¹`. -/
theorem phi11_equivariant (g : SU3) (t : tensorRep 1 1) :
    phi11 ((tensorRep 1 1).ρ g t) = g.1 * phi11 t * star g.1 :=
  phiT_equivariant g t


/-- The standard basis vector `eᵢ ∈ 3`. -/
noncomputable def ev (i : Fin 3) : fund := (Pi.single i 1 : Fin 3 → ℂ)
/-- The dual basis vector `eⱼ* ∈ 3̄`. -/
noncomputable def evd (j : Fin 3) : antifund := (LinearMap.proj j : (Fin 3 → ℂ) →ₗ[ℂ] ℂ)

theorem phiT_basis (i j : Fin 3) : phiT (ev i ⊗ₜ[ℂ] (evd j ⊗ₜ[ℂ] (1 : ℂ))) = E i j := by
  rw [phiT_tmul, one_smul]
  ext a b
  rw [pairMat_apply]
  change (Pi.single i 1 : Fin 3 → ℂ) a * (Pi.single b 1 : Fin 3 → ℂ) j = _
  simp only [Pi.single_apply, Matrix.single_apply]
  by_cases ha : i = a
  · subst ha
    by_cases hb : j = b <;> simp [hb]
  · have ha' : a ≠ i := Ne.symm ha
    simp [ha, ha']

theorem phiT_surjective : Function.Surjective phiT := by
  intro M
  refine ⟨∑ i, ∑ j, M i j • (ev i ⊗ₜ[ℂ] (evd j ⊗ₜ[ℂ] (1 : ℂ))), ?_⟩
  simp only [map_sum, map_smul, phiT_basis, Matrix.smul_single, smul_eq_mul, mul_one]
  exact (Matrix.matrix_eq_sum_single M).symm

theorem finrank_T11 : Module.finrank ℂ T11 = 9 := by
  have hf : Module.finrank ℂ fund = 3 := by
    change Module.finrank ℂ (Fin 3 → ℂ) = 3
    simp
  have ha : Module.finrank ℂ antifund = 3 := by
    change Module.finrank ℂ (Module.Dual ℂ (Fin 3 → ℂ)) = 3
    simp [Subspace.dual_finrank_eq]
  rw [Module.finrank_tensorProduct, Module.finrank_tensorProduct, hf, ha, Module.finrank_self]

theorem phiT_bijective : Function.Bijective phiT := by
  refine ⟨?_, phiT_surjective⟩
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).2 phiT_surjective
  rw [finrank_T11, Module.finrank_matrix, Fintype.card_fin, Module.finrank_self]

theorem phi11_injective : Function.Injective phi11 := phiT_bijective.1

theorem phi11_hw : phi11 (hwVec 1 1) = E 0 2 := phiT_basis 0 2

/-- The contraction `3 ⊗ 3̄ ⊗ 𝟙 → ℂ`. -/
noncomputable def contract11 : tensorRep 1 1 →ₗ[ℂ] ℂ :=
  Matrix.traceLinearMap (Fin 3) ℂ ℂ ∘ₗ phi11

theorem contract11_tmul (x : fund) (φ : antifund) (c : ℂ) :
    contract11 (x ⊗ₜ[ℂ] (φ ⊗ₜ[ℂ] c) : T11) =
      c * (show Module.Dual ℂ (Fin 3 → ℂ) from φ) (show Fin 3 → ℂ from x) := by
  change Matrix.trace (phiT (x ⊗ₜ[ℂ] (φ ⊗ₜ[ℂ] c))) = _
  rw [phiT_tmul, Matrix.trace_smul, dual_expand _ (show Fin 3 → ℂ from x)]
  simp [Matrix.trace, Fin.sum_univ_three, pairMat_apply]


/-! ## `V(1, 1)` is the traceless part of `3 ⊗ 3̄` -/

theorem trace_ad (g : SU3) (M : Mat3) : (g.1 * M * star g.1).trace = M.trace := by
  have hu : star g.1 * g.1 = 1 :=
    (Matrix.mem_unitaryGroup_iff').1 (Matrix.mem_specialUnitaryGroup_iff.1 g.2).1
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hu, Matrix.one_mul]

theorem tracelessSub_adInvariant : AdInvariant tracelessSub := by
  intro g M hM
  rw [mem_tracelessSub, trace_ad]
  exact hM

theorem E02_ne_zero : E 0 2 ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) 2
  simp at this

theorem E02_traceless : (E 0 2).trace = 0 := by
  simp [Matrix.trace]

/-- The image `Φ(V(1, 1))` is Ad-invariant. -/
theorem map_irrepSub11_adInvariant : AdInvariant ((irrepSub 1 1).map phi11) := by
  rintro g _ ⟨t, ht, rfl⟩
  exact ⟨(tensorRep 1 1).ρ g t, irrepSub_invariant 1 1 g t ht, phi11_equivariant g t⟩

/-- **`Φ(V(1, 1))` is exactly the traceless matrices `sl₃`.** -/
theorem irrepSub11_map_eq : (irrepSub 1 1).map phi11 = tracelessSub := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.map_le_iff_le_comap]
    refine irrepSub_le 1 1 _ (fun g t ht => ?_) ?_
    · change phi11 ((tensorRep 1 1).ρ g t) ∈ tracelessSub
      rw [phi11_equivariant]
      exact tracelessSub_adInvariant g _ ht
    · change phi11 (hwVec 1 1) ∈ tracelessSub
      rw [phi11_hw]
      exact E02_traceless
  · exact traceless_le_of_adInvariant map_irrepSub11_adInvariant
      ⟨hwVec 1 1, hwVec_mem 1 1, phi11_hw⟩ E02_ne_zero E02_traceless

/-- `V(1, 1) = Φ⁻¹(sl₃)`. -/
theorem irrepSub11_eq_comap : irrepSub 1 1 = tracelessSub.comap phi11 := by
  rw [← irrepSub11_map_eq, Submodule.comap_map_eq_of_injective phi11_injective]

/-- **`V(1, 1)` is the kernel of the contraction `3 ⊗ 3̄ ⊗ 𝟙 → ℂ`.** -/
theorem irrepSub11_eq_ker_contract : irrepSub 1 1 = LinearMap.ker contract11 := by
  rw [irrepSub11_eq_comap, contract11, LinearMap.ker_comp]
  rfl

/-- The ambient space `3 ⊗ (3̄ ⊗ 𝟙)` has dimension `9`. -/
theorem finrank_tensorRep11 : Module.finrank ℂ (tensorRep 1 1) = 9 := finrank_T11

/-- **`dim V(1, 1) = 8`** (as a subspace). -/
theorem finrank_irrepSub11 : Module.finrank ℂ (irrepSub 1 1) = 8 := by
  rw [(Submodule.equivMapOfInjective phi11 phi11_injective (irrepSub 1 1)).finrank_eq,
    irrepSub11_map_eq, finrank_tracelessSub]

/-- **`dim V(1, 1) = 8`** (the representation). -/
theorem finrank_irrepRep11 : Module.finrank ℂ (irrepRep 1 1) = 8 := finrank_irrepSub11

/-- `V(1, 1)` is not 9-dimensional: it is a proper subspace of `3 ⊗ 3̄`. -/
theorem irrep11_finrank_ne_nine : Module.finrank ℂ (irrepRep 1 1) ≠ 9 := by
  rw [finrank_irrepRep11]
  norm_num

/-! ## From stable subspaces to `Simple` -/

/-- A nonzero representation whose only stable subspaces are `⊥` and `⊤` is `Simple`. -/
theorem simple_of_invariant (X : FDRep ℂ SU3) (hX : Nontrivial X)
    (h : ∀ W : Submodule ℂ X, (∀ g, ∀ w ∈ W, X.ρ g w ∈ W) → W = ⊥ ∨ W = ⊤) : Simple X := by
  refine ⟨fun {Y} f _ => ⟨fun hiso hf0 => ?_, fun hf0 => ?_⟩⟩
  · obtain ⟨x, hx⟩ := exists_ne (0 : X)
    obtain ⟨y, hy⟩ := (GaugeSupport.bijective_of_isIso f).2 x
    apply hx
    rw [← hy, hf0]
    rfl
  · let U : Submodule ℂ X := LinearMap.range f.hom.hom.hom
    have hU : ∀ g, ∀ x ∈ U, X.ρ g x ∈ U := by
      rintro g _ ⟨y, rfl⟩
      exact ⟨Y.ρ g y, congrArg (fun m => m.hom.hom y) (f.comm g)⟩
    rcases h U hU with hbot | htop
    · exfalso
      apply hf0
      ext y
      have : f.hom.hom.hom y ∈ U := ⟨y, rfl⟩
      rw [hbot, Submodule.mem_bot] at this
      exact this
    · refine GaugeSupport.isIso_of_bijective f ⟨GaugeSupport.injective_of_mono f, fun x => ?_⟩
      have : x ∈ U := htop ▸ Submodule.mem_top
      exact this

/-! ## `3`, `3̄`, `𝟙`, `V(1, 0)`, `V(0, 1)`, `V(0, 0)` are simple -/

theorem d1_mulVec (v : Fin 3 → ℂ) :
    Matrix.mulVec d1M v = fun k => if k = 0 then v 0 else -v k := by
  funext k
  fin_cases k <;> simp [d1M, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem cyc_mulVec (v : Fin 3 → ℂ) (k : Fin 3) : Matrix.mulVec cycMat v k = v (k - 1) := by
  fin_cases k <;> simp [cycMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  all_goals rfl

/-- **The only subspaces of `ℂ³` stable under every `g ∈ SU(3)` are `⊥` and `⊤`.** -/
theorem std_invariant_eq_bot_or_top (W : Submodule ℂ (Fin 3 → ℂ))
    (hW : ∀ g : SU3, ∀ w ∈ W, Matrix.mulVec g.1 w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases h : W = ⊥
  · exact Or.inl h
  right
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  have hc : ∀ u ∈ W, Matrix.mulVec cycMat u ∈ W := fun u hu => hW cyc u hu
  have hv : ∃ v ∈ W, v 0 ≠ 0 := by
    by_cases h0 : w 0 ≠ 0
    · exact ⟨w, hw, h0⟩
    by_cases h2 : w 2 ≠ 0
    · refine ⟨_, hc w hw, ?_⟩
      rw [cyc_mulVec]
      exact h2
    by_cases h1 : w 1 ≠ 0
    · refine ⟨_, hc _ (hc w hw), ?_⟩
      rw [cyc_mulVec, cyc_mulVec]
      exact h1
    exfalso
    push Not at h0 h1 h2
    apply hw0
    funext k
    fin_cases k
    · exact h0
    · exact h1
    · exact h2
  obtain ⟨v, hvW, hv0⟩ := hv
  have he0 : (Pi.single 0 1 : Fin 3 → ℂ) ∈ W := by
    have hs : v + Matrix.mulVec d1M v ∈ W := W.add_mem hvW (hW d1 v hvW)
    have heq : (2 * v 0)⁻¹ • (v + Matrix.mulVec d1M v) = Pi.single 0 1 := by
      rw [d1_mulVec]
      funext k
      fin_cases k <;> simp
      field_simp
      ring
    rw [← heq]
    exact W.smul_mem _ hs
  have he1 : (Pi.single 1 1 : Fin 3 → ℂ) ∈ W := by
    have := hc _ he0
    rwa [show Matrix.mulVec cycMat (Pi.single 0 1) = Pi.single 1 1 from fund_cyc_e0] at this
  have he2 : (Pi.single 2 1 : Fin 3 → ℂ) ∈ W := by
    have := hc _ he1
    rwa [show Matrix.mulVec cycMat (Pi.single 1 1) = Pi.single 2 1 from fund_cyc_e1] at this
  rw [eq_top_iff, ← span_std_basis, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact he0
  · exact he1
  · exact he2

/-- **The only SU(3)-stable subspaces of `3` are `⊥` and `⊤`.** -/
theorem fund_invariant_eq_bot_or_top (W : Submodule ℂ fund)
    (hW : ∀ g, ∀ w ∈ W, fund.ρ g w ∈ W) : W = ⊥ ∨ W = ⊤ :=
  std_invariant_eq_bot_or_top W hW

theorem nontrivial_fund : Nontrivial fund :=
  ⟨⟨e1, 0, fun h => by
    have := projFund_e1
    rw [h, map_zero] at this
    exact zero_ne_one this⟩⟩

/-- **`3` is simple.** -/
theorem simple_fund : Simple fund :=
  simple_of_invariant fund nontrivial_fund fund_invariant_eq_bot_or_top

/-- **`3̄` is simple** (the dual of a simple representation, `DualSimple`). -/
theorem simple_antifund : Simple antifund :=
  haveI := simple_fund
  GaugeSupport.dual_simple fund

/-- **`𝟙` is simple.** -/
theorem simple_unit : Simple (𝟙_ (FDRep ℂ SU3)) :=
  simple_of_invariant _ (inferInstanceAs (Nontrivial ℂ))
    (fun W _ => eq_bot_or_eq_top (show Submodule ℂ ℂ from W))

/-- **`V(1, 0)` is simple.** -/
theorem simple_irrep10 : Simple (irrepRep 1 0) :=
  haveI := simple_fund
  Simple.of_iso irrep10Iso

/-- **`V(0, 1)` is simple.** -/
theorem simple_irrep01 : Simple (irrepRep 0 1) :=
  haveI := simple_antifund
  Simple.of_iso irrep01Iso

/-- **`V(0, 0)` is simple.** -/
theorem simple_irrep00 : Simple (irrepRep 0 0) :=
  haveI := simple_unit
  Simple.of_iso irrep00Iso

/-! ## `V(1, 1)` is simple -/

/-- **The only SU(3)-stable subspaces of `V(1, 1)` are `⊥` and `⊤`.** -/
theorem irrep11_invariant_eq_bot_or_top (W : Submodule ℂ (irrepRep 1 1))
    (hW : ∀ g, ∀ w ∈ W, (irrepRep 1 1).ρ g w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases h : W = ⊥
  · exact Or.inl h
  right
  let f : (irrepSub 1 1) →ₗ[ℂ] Mat3 := phi11 ∘ₗ (irrepSub 1 1).subtype
  have hf : Function.Injective f := phi11_injective.comp Subtype.val_injective
  let S : Submodule ℂ Mat3 := (show Submodule ℂ (irrepSub 1 1) from W).map f
  have hS : AdInvariant S := by
    rintro g _ ⟨w, hw, rfl⟩
    refine ⟨(irrepRep 1 1).ρ g w, hW g w hw, ?_⟩
    exact phi11_equivariant g w.1
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  have hfw : f w ≠ 0 := fun h0 => hw0 (hf (h0.trans (map_zero f).symm))
  have hwT : f w ∈ tracelessSub := by
    rw [← irrepSub11_map_eq]
    exact ⟨w.1, w.2, rfl⟩
  have hTS := traceless_le_of_adInvariant hS ⟨w, hw, rfl⟩ hfw hwT
  rw [eq_top_iff]
  intro x _
  have hx : f x ∈ S := hTS (by rw [← irrepSub11_map_eq]; exact ⟨x.1, x.2, rfl⟩)
  obtain ⟨y, hy, hyx⟩ := hx
  rw [← hf hyx]
  exact hy

/-- **`V(1, 1)`, the adjoint, is simple.** -/
theorem simple_irrep11 : Simple (irrepRep 1 1) :=
  simple_of_invariant _ ⟨⟨hwIrrep 1 1, 0, hwIrrep_ne_zero 1 1⟩⟩ irrep11_invariant_eq_bot_or_top

end IrrepIrreducibleSU3
