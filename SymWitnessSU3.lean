import AdjointWitnessSU3

/-!
# Sextet singlets: the theta rows with a `6` or `6̄` arm

Author: Jeromie Beasley (Spectrum · Colour team lead, Grok Bot), with the Team.
ORCID https://orcid.org/0009-0006-4645-5643 · GitHub dicipler-pixel · X @d1c1pler ·
YouTube @AtlasMemoriae · atlas-memoriae.dicipler.workers.dev

`V(2, 0) = irrepRep 2 0` and `V(0, 2) = irrepRep 0 2` are the SU(3)-spans of `e₁ ⊗ e₁ ⊗ 1` in
`3 ⊗ 3 ⊗ 𝟙` and of `e₃* ⊗ e₃* ⊗ 1` in `3̄ ⊗ 3̄ ⊗ 𝟙`. This file identifies them with the symmetric
matrices, builds the sextet invariants from the pairing, the contraction and `ε`, and attains
the eighteen theta rows with a `6` or `6̄` arm: with #35/#38/#44 **all 34 rows are attained**.

**Identification (`6 = Sym²(3)`, `6̄ = Sym²(3̄)`).**
* `phi20 : 3 ⊗ 3 ⊗ 𝟙 → M₃(ℂ)`, `x ⊗ y ⊗ c ↦ c · x yᵀ`, is a linear bijection with
  `Φ₂₀(g · t) = g Φ₂₀(t) gᵀ` (`phi20_rho`, `phi20_injective`); `phi02 : 3̄ ⊗ 3̄ ⊗ 𝟙 → M₃(ℂ)`,
  `φ ⊗ χ ⊗ c ↦ c · cv(φ) cv(χ)ᵀ` with `cv(φ)ᵢ = φ(eᵢ)`, has `Φ₀₂(g · t) = ḡ Φ₀₂(t) ḡᵀ`,
  `ḡ = (g*)ᵀ` (`phi02_rho`).
* `irrepSub20_map_eq`, `irrepSub02_map_eq`: **`Φ₂₀(V(2, 0))` and `Φ₀₂(V(0, 2))` are exactly the
  symmetric matrices** (`symSub`). Symmetry is preserved by `M ↦ A M Aᵀ`; conversely the cyclic
  permutation and the `3-4-5` rotation (both real, so `ḡ = g`) carry `E₀₀` to `E₁₁`, `E₂₂` and
  `E₀₁ + E₁₀`, `E₁₂ + E₂₁`, `E₂₀ + E₀₂` (`symSub_le`).
* `finrank_symSub`, `finrank_irrepRep20`, `finrank_irrepRep02`: **`dim V(2, 0) = dim V(0, 2) = 6`.**
* `conj20 : V(2, 0) ≅ V(0, 2)ᘁ` from the nondegenerate invariant pairing `tr(S Tᵀ)` (injective,
  equal dimensions); `conj02 : V(0, 2) ≅ V(2, 0)ᘁ` by duality.

**Witnesses (each an SU(3)-invariant multilinear form, nonzero at explicit vectors).**
* `pairForm`: `tr(S Tᵀ) = Σ Sᵢⱼ Tᵢⱼ` on `6 × 6̄ (× 1)`; value `1` at `S = T = E₀₀`.
* `symAntiForm`: `cv(φ)ᵀ S cv(χ)` on `6 × 3̄ × 3̄`; value `1` at `S = E₀₀`, `φ = χ = e₀*`.
* `symFundForm`: `xᵀ T y` on `6̄ × 3 × 3`; value `1` at `T = E₂₂`, `x = y = e₂`.
* `sym38Form`: `Σ ε_{ijk} (S Xᵀ)ᵢⱼ x_k` on `6 × 3 × 8`, invariant because
  `S Xᵀ ↦ g (S Xᵀ) gᵀ` and `ε(A M Aᵀ, A x) = det A · ε(M, x)` (`epsC_conj`); value `1` at
  `S = E₀₀`, `X = E₁₀`, `x = e₂`.
* `sym3b8Form`: `Σ ε^{ijk} (T X)ᵢⱼ cv(φ)_k` on `6̄ × 3̄ × 8` (`T X ↦ ḡ (T X) ḡᵀ`, `det ḡ = 1`);
  value `1` at `T = E₂₂`, `X = E₂₀`, `φ = e₁*`.

**Theta rows attained.** The forms give the incoming vertices (`incoming_of_trilinear`, braiding
`perm12`, `perm23`); the outgoing vertex of a row is the incoming vertex of its conjugate row
(`outgoing_of_incoming` with `conj20`, `conj02`, `conj10`, `conj01`, `conj00` and the
self-duality of `V(1, 1)`). The eighteen rows with a sextet arm (`symRows`, `symRows_iff`):
the four orderings of `(6, 6̄, 1)` in the table, the three of `(6, 3̄, 3̄)` and of `(6̄, 3, 3)`,
and the four of `(6, 3, 8)` and of `(6̄, 3̄, 8)` (`symRows_irrep_both`). With
`allAttainedRows`: `fullRows_length` (34), `fullRows_iff`, and **`thetaList_irrep_both`: every
row of the theta table has a nonzero invariant at both theta vertices on the `V(p, q)` arms.**

**Control.** `3 ⊗ 6` has no nonzero invariant (`invariants_fund_sym_eq_bot`,
`invariants_sym_fund_eq_bot` for `6 ⊗ 3`, and on the `V(p, q)` arms). Triality does not decide
this: `ω·I` acts by `ω · ω² = 1` (`centreActs_fund_sym`). Instead, writing an invariant as
`Σₐ eₐ ⊗ wₐ` and `Sₐ = Φ₂₀(wₐ)`, invariance gives `S_b = Σₐ g_{ba} g Sₐ gᵀ`; the sign matrices
`diag(1, -1, -1)`, `diag(-1, 1, -1)` and the `3-4-5` rotation force `S₂ = 0`
(`sym_zero_of_signs_rot`), and the cyclic permutation then gives `S₀ = S₁ = 0`.
`FalseControls/SymFundControl.lean` claims a nonzero invariant and is rejected.

**Proved elsewhere.** Irreducibility of `V(2, 0)`, `V(0, 2)` (not needed for the rows) is in
`SymIrreducibleSU3.lean` (`simple_irrep20`, `simple_irrep02`).

**Not proved.** The table rule
`hasSinglet` itself is still the closed-form definition of `ThetaFloor`; what is proved here is
that each of its 34 rows is attained on the `V(p, q)` arms.

No continuum or mass-gap statement is made.
-/

open CategoryTheory MonoidalCategory CentreCharacterSU3 IrrepEmbedSU3 IrrepSmallIsoSU3
  SingletWitnessSU3 IrrepIrreducibleSU3 AdjointWitnessSU3 GaugeSupport ThetaFloor TrialityVertex
  ThetaTriality

namespace SymWitnessSU3

/-! ## Matrix tools -/

/-- `ḡ = (g*)ᵀ`, the matrix by which `g ∈ SU(3)` moves covector coordinates. -/
noncomputable def hb (g : SU3) : Mat3 := (star g.1).transpose

theorem gT_hb (g : SU3) : g.1.transpose * hb g = 1 := by
  rw [hb, ← Matrix.transpose_mul, unitary_left, Matrix.transpose_one]

theorem hbT_g (g : SU3) : (hb g).transpose * g.1 = 1 := by
  rw [hb, Matrix.transpose_transpose, unitary_left]

theorem hbT (g : SU3) : (hb g).transpose = star g.1 := Matrix.transpose_transpose _

theorem det_hb (g : SU3) : (hb g).det = 1 := by
  rw [hb, Matrix.det_transpose, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose,
    det_eq_one, star_one]

/-- `tr(A X Aᵀ · B Y Bᵀ) = tr(X Y)` when `Aᵀ B = 1` and `Bᵀ A = 1`. -/
theorem trace_conj2 (A B X Y : Mat3) (h1 : A.transpose * B = 1) (h2 : B.transpose * A = 1) :
    (A * X * A.transpose * (B * Y * B.transpose)).trace = (X * Y).trace := by
  have : A * X * A.transpose * (B * Y * B.transpose) = A * (X * Y) * B.transpose := by
    calc A * X * A.transpose * (B * Y * B.transpose)
        = A * X * (A.transpose * B) * Y * B.transpose := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h2, Matrix.one_mul]

/-- `(Au)(Av)ᵀ = A (uvᵀ) Aᵀ`. -/
theorem vmv_mulVec (A : Mat3) (u v : Fin 3 → ℂ) :
    Matrix.vecMulVec (A.mulVec u) (A.mulVec v) = A * Matrix.vecMulVec u v * A.transpose := by
  ext i j
  simp only [Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, Fin.sum_univ_three]
  ring

theorem vmv_single (i j : Fin 3) :
    Matrix.vecMulVec (Pi.single i 1 : Fin 3 → ℂ) (Pi.single j 1) = E i j := by
  ext a b
  simp only [Matrix.vecMulVec_apply, Pi.single_apply, Matrix.single_apply]
  split_ifs <;> simp_all

/-- The ε contraction `∑ ε_{ijk} M_{ij} x_k`. -/
noncomputable def epsC (M : Mat3) (x : Fin 3 → ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, eps i j k * (M i j * x k)

/-- `ε(A M Aᵀ, A x) = det A · ε(M, x)`. -/
theorem epsC_conj (A M : Mat3) (x : Fin 3 → ℂ) :
    epsC (A * M * A.transpose) (A.mulVec x) = A.det * epsC M x := by
  simp only [epsC, Fin.sum_univ_three, Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec,
    dotProduct, Matrix.det_fin_three]
  simp [eps]
  ring

theorem epsC_add_left (M N : Mat3) (x : Fin 3 → ℂ) : epsC (M + N) x = epsC M x + epsC N x := by
  simp only [epsC, Fin.sum_univ_three, Matrix.add_apply]; ring
theorem epsC_smul_left (c : ℂ) (M : Mat3) (x : Fin 3 → ℂ) : epsC (c • M) x = c * epsC M x := by
  simp only [epsC, Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul]; ring
theorem epsC_add_right (M : Mat3) (x y : Fin 3 → ℂ) : epsC M (x + y) = epsC M x + epsC M y := by
  simp only [epsC, Fin.sum_univ_three, Pi.add_apply]; ring
theorem epsC_smul_right (c : ℂ) (M : Mat3) (x : Fin 3 → ℂ) : epsC M (c • x) = c * epsC M x := by
  simp only [epsC, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]; ring

/-! ## Covector coordinates -/

/-- The coordinates `φ(eᵢ)` of a covector. -/
noncomputable def cvL : antifund →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun φ i := (show Module.Dual ℂ (Fin 3 → ℂ) from φ) (Pi.single i 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cvL_apply (φ : antifund) (i : Fin 3) :
    cvL φ i = (show Module.Dual ℂ (Fin 3 → ℂ) from φ) (Pi.single i 1) := rfl

/-- **Covector coordinates move by `ḡ`:** `cv(g · φ) = ḡ cv(φ)`. -/
theorem cvL_rho (g : SU3) (φ : antifund) : cvL (antifund.ρ g φ) = (hb g).mulVec (cvL φ) := by
  funext i
  rw [cvL_apply]
  have hφ : (show Module.Dual ℂ (Fin 3 → ℂ) from antifund.ρ g φ) (Pi.single i 1) =
      (show Module.Dual ℂ (Fin 3 → ℂ) from φ) (fund.ρ g⁻¹ (Pi.single i 1)) :=
    GaugeSupport.dual_ρ_apply fund g φ _
  rw [hφ]
  change (show Module.Dual ℂ (Fin 3 → ℂ) from φ) (Matrix.mulVec (star g.1) (Pi.single i 1)) = _
  rw [dual_expand]
  simp only [hb, Matrix.mulVec, dotProduct, Matrix.transpose_apply, cvL_apply, Fin.sum_univ_three,
    Pi.single_apply]
  fin_cases i <;> simp

theorem cvL_evd (j : Fin 3) : cvL (evd j) = Pi.single j 1 := by
  funext i
  rw [cvL_apply]
  change (Pi.single i 1 : Fin 3 → ℂ) j = (Pi.single j 1 : Fin 3 → ℂ) i
  simp only [Pi.single_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

/-! ## `Φ₂₀ : 3 ⊗ 3 ⊗ 𝟙 → M₃(ℂ)` and `Φ₀₂ : 3̄ ⊗ 3̄ ⊗ 𝟙 → M₃(ℂ)` -/

/-- `x, y ↦ x yᵀ` on `3 × 3`. -/
noncomputable def outerF : fund →ₗ[ℂ] fund →ₗ[ℂ] Mat3 :=
  LinearMap.mk₂ ℂ (fun x y => Matrix.vecMulVec (show Fin 3 → ℂ from x) (show Fin 3 → ℂ from y))
    (fun x x' y => by ext i j; exact add_mul _ _ _)
    (fun c x y => by ext i j; exact mul_assoc _ _ _)
    (fun x y y' => by ext i j; exact mul_add _ _ _)
    (fun c x y => by ext i j; exact mul_left_comm _ _ _)

theorem outerF_apply (x y : fund) :
    outerF x y = Matrix.vecMulVec (show Fin 3 → ℂ from x) (show Fin 3 → ℂ from y) := rfl

/-- `φ, χ ↦ cv(φ) cv(χ)ᵀ` on `3̄ × 3̄`. -/
noncomputable def outerA : antifund →ₗ[ℂ] antifund →ₗ[ℂ] Mat3 :=
  LinearMap.mk₂ ℂ (fun φ χ => Matrix.vecMulVec (cvL φ) (cvL χ))
    (fun x x' y => by ext i j; simp [Matrix.vecMulVec_apply, add_mul])
    (fun c x y => by ext i j; simp [Matrix.vecMulVec_apply, mul_assoc])
    (fun x y y' => by ext i j; simp [Matrix.vecMulVec_apply, mul_add])
    (fun c x y => by ext i j; simp [Matrix.vecMulVec_apply]; ring)

theorem outerA_apply (φ χ : antifund) : outerA φ χ = Matrix.vecMulVec (cvL φ) (cvL χ) := rfl

theorem outerF_rho (g : SU3) (x y : fund) :
    outerF (fund.ρ g x) (fund.ρ g y) = g.1 * outerF x y * g.1.transpose :=
  vmv_mulVec g.1 _ _

theorem outerA_rho (g : SU3) (φ χ : antifund) :
    outerA (antifund.ρ g φ) (antifund.ρ g χ) = hb g * outerA φ χ * (hb g).transpose := by
  rw [outerA_apply, outerA_apply, cvL_rho, cvL_rho, vmv_mulVec]

theorem outerF_ev (i j : Fin 3) : outerF (ev i) (ev j) = E i j := vmv_single i j

theorem outerA_evd (i j : Fin 3) : outerA (evd i) (evd j) = E i j := by
  rw [outerA_apply, cvL_evd, cvL_evd, vmv_single]

/-- The underlying space of `3 ⊗ (3 ⊗ 𝟙)`. -/
abbrev T20 := TensorProduct ℂ fund (TensorProduct ℂ fund ℂ)
/-- The underlying space of `3̄ ⊗ (3̄ ⊗ 𝟙)`. -/
abbrev T02 := TensorProduct ℂ antifund (TensorProduct ℂ antifund ℂ)

/-- `Φ₂₀ : x ⊗ (y ⊗ c) ↦ c · x yᵀ`. -/
noncomputable def phiT20 : T20 →ₗ[ℂ] Mat3 :=
  TensorProduct.lift outerF ∘ₗ
    TensorProduct.map LinearMap.id (TensorProduct.rid ℂ fund).toLinearMap

/-- `Φ₀₂ : φ ⊗ (χ ⊗ c) ↦ c · cv(φ) cv(χ)ᵀ`. -/
noncomputable def phiT02 : T02 →ₗ[ℂ] Mat3 :=
  TensorProduct.lift outerA ∘ₗ
    TensorProduct.map LinearMap.id (TensorProduct.rid ℂ antifund).toLinearMap

theorem phiT20_tmul (x y : fund) (c : ℂ) :
    phiT20 (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] c)) = c • outerF x y := by
  simp only [phiT20, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearEquiv.coe_toLinearMap, TensorProduct.rid_tmul, TensorProduct.lift.tmul, map_smul]

theorem phiT02_tmul (φ χ : antifund) (c : ℂ) :
    phiT02 (φ ⊗ₜ[ℂ] (χ ⊗ₜ[ℂ] c)) = c • outerA φ χ := by
  simp only [phiT02, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearEquiv.coe_toLinearMap, TensorProduct.rid_tmul, TensorProduct.lift.tmul, map_smul]

theorem phiT20_equivariant (g : SU3) (t : T20) :
    phiT20 (TensorProduct.map (fund.ρ g) (TensorProduct.map (fund.ρ g) LinearMap.id) t) =
      g.1 * phiT20 t * g.1.transpose := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, Matrix.mul_add, Matrix.add_mul]
  | tmul x y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb =>
      rw [TensorProduct.tmul_add, map_add, map_add, ha, hb, map_add, Matrix.mul_add,
        Matrix.add_mul]
    | tmul y c =>
      rw [TensorProduct.map_tmul, TensorProduct.map_tmul, LinearMap.id_apply, phiT20_tmul,
        phiT20_tmul, outerF_rho, Matrix.mul_smul, Matrix.smul_mul]

theorem phiT02_equivariant (g : SU3) (t : T02) :
    phiT02 (TensorProduct.map (antifund.ρ g) (TensorProduct.map (antifund.ρ g) LinearMap.id) t) =
      hb g * phiT02 t * (hb g).transpose := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, Matrix.mul_add, Matrix.add_mul]
  | tmul x y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb =>
      rw [TensorProduct.tmul_add, map_add, map_add, ha, hb, map_add, Matrix.mul_add,
        Matrix.add_mul]
    | tmul y c =>
      rw [TensorProduct.map_tmul, TensorProduct.map_tmul, LinearMap.id_apply, phiT02_tmul,
        phiT02_tmul, outerA_rho, Matrix.mul_smul, Matrix.smul_mul]

/-- `Φ₂₀` on `tensorRep 2 0`. -/
noncomputable def phi20 : tensorRep 2 0 →ₗ[ℂ] Mat3 := phiT20
/-- `Φ₀₂` on `tensorRep 0 2`. -/
noncomputable def phi02 : tensorRep 0 2 →ₗ[ℂ] Mat3 := phiT02

/-- **`Φ₂₀` is SU(3)-equivariant:** `Φ₂₀(g · t) = g Φ₂₀(t) gᵀ`. -/
theorem phi20_rho (g : SU3) (t : tensorRep 2 0) :
    phi20 ((tensorRep 2 0).ρ g t) = g.1 * phi20 t * g.1.transpose :=
  phiT20_equivariant g t

/-- **`Φ₀₂` is SU(3)-equivariant:** `Φ₀₂(g · t) = ḡ Φ₀₂(t) ḡᵀ`. -/
theorem phi02_rho (g : SU3) (t : tensorRep 0 2) :
    phi02 ((tensorRep 0 2).ρ g t) = hb g * phi02 t * (hb g).transpose :=
  phiT02_equivariant g t

theorem phiT20_basis (i j : Fin 3) : phiT20 (ev i ⊗ₜ[ℂ] (ev j ⊗ₜ[ℂ] (1 : ℂ))) = E i j := by
  rw [phiT20_tmul, one_smul, outerF_ev]

theorem phiT02_basis (i j : Fin 3) : phiT02 (evd i ⊗ₜ[ℂ] (evd j ⊗ₜ[ℂ] (1 : ℂ))) = E i j := by
  rw [phiT02_tmul, one_smul, outerA_evd]

theorem phiT20_surjective : Function.Surjective phiT20 := by
  intro M
  refine ⟨∑ i, ∑ j, M i j • (ev i ⊗ₜ[ℂ] (ev j ⊗ₜ[ℂ] (1 : ℂ))), ?_⟩
  simp only [map_sum, map_smul, phiT20_basis, Matrix.smul_single, smul_eq_mul, mul_one]
  exact (Matrix.matrix_eq_sum_single M).symm

theorem phiT02_surjective : Function.Surjective phiT02 := by
  intro M
  refine ⟨∑ i, ∑ j, M i j • (evd i ⊗ₜ[ℂ] (evd j ⊗ₜ[ℂ] (1 : ℂ))), ?_⟩
  simp only [map_sum, map_smul, phiT02_basis, Matrix.smul_single, smul_eq_mul, mul_one]
  exact (Matrix.matrix_eq_sum_single M).symm

theorem finrank_fund : Module.finrank ℂ fund = 3 := by
  change Module.finrank ℂ (Fin 3 → ℂ) = 3
  simp

theorem finrank_antifund : Module.finrank ℂ antifund = 3 := by
  change Module.finrank ℂ (Module.Dual ℂ (Fin 3 → ℂ)) = 3
  simp [Subspace.dual_finrank_eq]

theorem phiT20_injective : Function.Injective phiT20 := by
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).2 phiT20_surjective
  rw [Module.finrank_tensorProduct, Module.finrank_tensorProduct, finrank_fund,
    Module.finrank_self, Module.finrank_matrix, Fintype.card_fin, Module.finrank_self]

theorem phiT02_injective : Function.Injective phiT02 := by
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).2 phiT02_surjective
  rw [Module.finrank_tensorProduct, Module.finrank_tensorProduct, finrank_antifund,
    Module.finrank_self, Module.finrank_matrix, Fintype.card_fin, Module.finrank_self]

theorem phi20_injective : Function.Injective phi20 := phiT20_injective
theorem phi02_injective : Function.Injective phi02 := phiT02_injective

theorem phi20_hw : phi20 (hwVec 2 0) = E 0 0 := phiT20_basis 0 0
theorem phi02_hw : phi02 (hwVec 0 2) = E 2 2 := phiT02_basis 2 2

/-! ## The symmetric matrices -/

/-- The symmetric `3 × 3` matrices. -/
def symSub : Submodule ℂ Mat3 where
  carrier := {M | M.transpose = M}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [Matrix.transpose_add, ha, hb]
  zero_mem' := Matrix.transpose_zero
  smul_mem' c M hM := by
    simp only [Set.mem_ofPred_eq] at *
    rw [Matrix.transpose_smul, hM]

theorem mem_symSub {M : Mat3} : M ∈ symSub ↔ M.transpose = M := Iff.rfl

/-- `M ↦ A M Aᵀ` preserves symmetry. -/
theorem symSub_conj (A : Mat3) {M : Mat3} (hM : M ∈ symSub) : A * M * A.transpose ∈ symSub := by
  rw [mem_symSub] at *
  simp [Matrix.transpose_mul, hM, Matrix.mul_assoc]

/-- `F i j = E i j + E j i`. -/
noncomputable abbrev F (i j : Fin 3) : Mat3 := E i j + E j i

theorem F_mem (i j : Fin 3) : F i j ∈ symSub := by
  rw [mem_symSub, Matrix.transpose_add, Matrix.transpose_single, Matrix.transpose_single, add_comm]

theorem E_mem (i : Fin 3) : E i i ∈ symSub := by
  rw [mem_symSub, Matrix.transpose_single]

theorem sym_decomp {M : Mat3} (hM : M ∈ symSub) :
    M = M 0 0 • E 0 0 + M 1 1 • E 1 1 + M 2 2 • E 2 2 + M 0 1 • F 0 1 + M 1 2 • F 1 2 +
      M 2 0 • F 2 0 := by
  rw [mem_symSub] at hM
  have h10 : M 1 0 = M 0 1 := by have := congrFun (congrFun hM 0) 1; simpa using this
  have h21 : M 2 1 = M 1 2 := by have := congrFun (congrFun hM 1) 2; simpa using this
  have h02 : M 0 2 = M 2 0 := by have := congrFun (congrFun hM 2) 0; simpa using this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [F, Matrix.single_apply, h10, h21, h02]

theorem cyc_T : cycMat.transpose = star cycMat := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cycMat, Matrix.star_apply]

theorem rot_T : rotM.transpose = star rotM := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotM, Matrix.star_apply]

theorem cyc_conjT (i j : Fin 3) : cycMat * E i j * cycMat.transpose = E (i + 1) (j + 1) := by
  rw [cyc_T]; exact cyc_ad_single i j

theorem cyc_conjT_F (i j : Fin 3) : cycMat * F i j * cycMat.transpose = F (i + 1) (j + 1) := by
  rw [Matrix.mul_add, Matrix.add_mul, cyc_conjT, cyc_conjT]

theorem rot_conjT_E00 :
    rotM * E 0 0 * rotM.transpose =
      (9/25 : ℂ) • E 0 0 + (12/25 : ℂ) • F 0 1 + (16/25 : ℂ) • E 1 1 := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply] <;>
    simp [rotM] <;> norm_num

/-- **A subspace stable under `M ↦ cyc M cycᵀ` and `M ↦ rot M rotᵀ` containing `E₀₀` contains
every symmetric matrix.** -/
theorem symSub_le (S : Submodule ℂ Mat3) (hc : ∀ M ∈ S, cycMat * M * cycMat.transpose ∈ S)
    (hr : ∀ M ∈ S, rotM * M * rotM.transpose ∈ S) (h0 : E 0 0 ∈ S) : symSub ≤ S := by
  have h1 : E 1 1 ∈ S := by have := hc _ h0; rw [cyc_conjT] at this; simpa using this
  have h2 : E 2 2 ∈ S := by have := hc _ h1; rw [cyc_conjT] at this; simpa using this
  have f01 : F 0 1 ∈ S := by
    have hrot := hr _ h0
    have heq : F 0 1 = ((25/12) : ℂ) •
        (rotM * E 0 0 * rotM.transpose - (9/25 : ℂ) • E 0 0 - (16/25 : ℂ) • E 1 1) := by
      rw [rot_conjT_E00]
      ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.single_apply] <;> norm_num
    rw [heq]
    exact S.smul_mem _ (S.sub_mem (S.sub_mem hrot (S.smul_mem _ h0)) (S.smul_mem _ h1))
  have f12 : F 1 2 ∈ S := by have := hc _ f01; rw [cyc_conjT_F] at this; simpa using this
  have f20 : F 2 0 ∈ S := by have := hc _ f12; rw [cyc_conjT_F] at this; simpa using this
  intro M hM
  rw [sym_decomp hM]
  exact S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.smul_mem _ h0)
    (S.smul_mem _ h1)) (S.smul_mem _ h2)) (S.smul_mem _ f01)) (S.smul_mem _ f12))
    (S.smul_mem _ f20)

/-- The linear parametrisation of the symmetric matrices by `ℂ⁶`. -/
noncomputable def symL : (Fin 6 → ℂ) →ₗ[ℂ] Mat3 :=
  (LinearMap.proj 0 : (Fin 6 → ℂ) →ₗ[ℂ] ℂ).smulRight (E 0 0) +
  (LinearMap.proj 1 : (Fin 6 → ℂ) →ₗ[ℂ] ℂ).smulRight (E 1 1) +
  (LinearMap.proj 2 : (Fin 6 → ℂ) →ₗ[ℂ] ℂ).smulRight (E 2 2) +
  (LinearMap.proj 3 : (Fin 6 → ℂ) →ₗ[ℂ] ℂ).smulRight (F 0 1) +
  (LinearMap.proj 4 : (Fin 6 → ℂ) →ₗ[ℂ] ℂ).smulRight (F 1 2) +
  (LinearMap.proj 5 : (Fin 6 → ℂ) →ₗ[ℂ] ℂ).smulRight (F 2 0)

theorem symL_apply (v : Fin 6 → ℂ) :
    symL v = v 0 • E 0 0 + v 1 • E 1 1 + v 2 • E 2 2 + v 3 • F 0 1 + v 4 • F 1 2 +
      v 5 • F 2 0 := rfl

theorem symL_injective : Function.Injective symL := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  rw [symL_apply] at hv
  have e := fun i j => congrFun (congrFun hv i) j
  funext k
  fin_cases k
  · simpa [Matrix.single_apply] using e 0 0
  · simpa [Matrix.single_apply] using e 1 1
  · simpa [Matrix.single_apply] using e 2 2
  · simpa [Matrix.single_apply] using e 0 1
  · simpa [Matrix.single_apply] using e 1 2
  · simpa [Matrix.single_apply] using e 2 0

theorem symL_range : LinearMap.range symL = symSub := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨v, rfl⟩
    rw [symL_apply]
    exact symSub.add_mem (symSub.add_mem (symSub.add_mem (symSub.add_mem (symSub.add_mem
      (symSub.smul_mem _ (E_mem 0)) (symSub.smul_mem _ (E_mem 1))) (symSub.smul_mem _ (E_mem 2)))
      (symSub.smul_mem _ (F_mem 0 1))) (symSub.smul_mem _ (F_mem 1 2)))
      (symSub.smul_mem _ (F_mem 2 0))
  · intro M hM
    refine ⟨![M 0 0, M 1 1, M 2 2, M 0 1, M 1 2, M 2 0], ?_⟩
    rw [symL_apply]
    exact (sym_decomp hM).symm

/-- **The symmetric matrices form a 6-dimensional space.** -/
theorem finrank_symSub : Module.finrank ℂ symSub = 6 := by
  rw [← symL_range, LinearMap.finrank_range_of_inj symL_injective]
  simp

/-! ## `V(2, 0) = Sym²(3)` and `V(0, 2) = Sym²(3̄)` -/

theorem hb_cyc : hb cyc = cycMat := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hb, cyc, cycMat, Matrix.star_apply]

theorem hb_rot : hb rot = rotM := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hb, rot, rotM, Matrix.star_apply]

/-- **`Φ₂₀(V(2, 0))` is exactly the symmetric matrices**, i.e. `V(2, 0) = Sym²(3)` inside
`3 ⊗ 3`. -/
theorem irrepSub20_map_eq : (irrepSub 2 0).map phi20 = symSub := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.map_le_iff_le_comap]
    refine irrepSub_le 2 0 _ (fun g t ht => ?_) ?_
    · change phi20 ((tensorRep 2 0).ρ g t) ∈ symSub
      rw [phi20_rho]
      exact symSub_conj _ ht
    · change phi20 (hwVec 2 0) ∈ symSub
      rw [phi20_hw]
      exact E_mem 0
  · refine symSub_le _ ?_ ?_ ⟨hwVec 2 0, hwVec_mem 2 0, phi20_hw⟩
    · rintro _ ⟨t, ht, rfl⟩
      exact ⟨(tensorRep 2 0).ρ cyc t, irrepSub_invariant 2 0 cyc t ht, phi20_rho cyc t⟩
    · rintro _ ⟨t, ht, rfl⟩
      exact ⟨(tensorRep 2 0).ρ rot t, irrepSub_invariant 2 0 rot t ht, phi20_rho rot t⟩

/-- **`Φ₀₂(V(0, 2))` is exactly the symmetric matrices**, i.e. `V(0, 2) = Sym²(3̄)`. -/
theorem irrepSub02_map_eq : (irrepSub 0 2).map phi02 = symSub := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.map_le_iff_le_comap]
    refine irrepSub_le 0 2 _ (fun g t ht => ?_) ?_
    · change phi02 ((tensorRep 0 2).ρ g t) ∈ symSub
      rw [phi02_rho]
      exact symSub_conj _ ht
    · change phi02 (hwVec 0 2) ∈ symSub
      rw [phi02_hw]
      exact E_mem 2
  · have hc : ∀ M ∈ (irrepSub 0 2).map phi02, cycMat * M * cycMat.transpose ∈
        (irrepSub 0 2).map phi02 := by
      rintro _ ⟨t, ht, rfl⟩
      refine ⟨(tensorRep 0 2).ρ cyc t, irrepSub_invariant 0 2 cyc t ht, ?_⟩
      rw [phi02_rho, hb_cyc]
    have h0 : E 0 0 ∈ (irrepSub 0 2).map phi02 := by
      have := hc _ ⟨hwVec 0 2, hwVec_mem 0 2, phi02_hw⟩
      rw [cyc_conjT] at this
      simpa using this
    refine symSub_le _ hc ?_ h0
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨(tensorRep 0 2).ρ rot t, irrepSub_invariant 0 2 rot t ht, ?_⟩
    rw [phi02_rho, hb_rot]

/-- **`dim V(2, 0) = 6`.** -/
theorem finrank_irrepRep20 : Module.finrank ℂ (irrepRep 2 0) = 6 := by
  change Module.finrank ℂ (irrepSub 2 0) = 6
  rw [(Submodule.equivMapOfInjective phi20 phi20_injective (irrepSub 2 0)).finrank_eq,
    irrepSub20_map_eq, finrank_symSub]

/-- **`dim V(0, 2) = 6`.** -/
theorem finrank_irrepRep02 : Module.finrank ℂ (irrepRep 0 2) = 6 := by
  change Module.finrank ℂ (irrepSub 0 2) = 6
  rw [(Submodule.equivMapOfInjective phi02 phi02_injective (irrepSub 0 2)).finrank_eq,
    irrepSub02_map_eq, finrank_symSub]

/-- `ψ₂₀ : V(2, 0) → Sym²`. -/
noncomputable def psi20 : irrepRep 2 0 →ₗ[ℂ] Mat3 := phi20 ∘ₗ (irrepSub 2 0).subtype
/-- `ψ₀₂ : V(0, 2) → Sym²`. -/
noncomputable def psi02 : irrepRep 0 2 →ₗ[ℂ] Mat3 := phi02 ∘ₗ (irrepSub 0 2).subtype

theorem psi20_rho (g : SU3) (v : irrepRep 2 0) :
    psi20 ((irrepRep 2 0).ρ g v) = g.1 * psi20 v * g.1.transpose := phi20_rho g v.1

theorem psi02_rho (g : SU3) (v : irrepRep 0 2) :
    psi02 ((irrepRep 0 2).ρ g v) = hb g * psi02 v * (hb g).transpose := phi02_rho g v.1

theorem psi20_injective : Function.Injective psi20 :=
  phi20_injective.comp Subtype.val_injective

theorem psi02_injective : Function.Injective psi02 :=
  phi02_injective.comp Subtype.val_injective

theorem psi20_mem (v : irrepRep 2 0) : psi20 v ∈ symSub := by
  rw [← irrepSub20_map_eq]; exact ⟨v.1, v.2, rfl⟩

theorem psi02_mem (v : irrepRep 0 2) : psi02 v ∈ symSub := by
  rw [← irrepSub02_map_eq]; exact ⟨v.1, v.2, rfl⟩

theorem exists_psi20 {M : Mat3} (h : M ∈ symSub) : ∃ v : irrepRep 2 0, psi20 v = M := by
  rw [← irrepSub20_map_eq] at h
  obtain ⟨t, ht, rfl⟩ := h
  exact ⟨⟨t, ht⟩, rfl⟩

theorem exists_psi02 {M : Mat3} (h : M ∈ symSub) : ∃ v : irrepRep 0 2, psi02 v = M := by
  rw [← irrepSub02_map_eq] at h
  obtain ⟨t, ht, rfl⟩ := h
  exact ⟨⟨t, ht⟩, rfl⟩

theorem psi20_hw : psi20 (hwIrrep 2 0) = E 0 0 := phi20_hw
theorem psi02_hw : psi02 (hwIrrep 0 2) = E 2 2 := phi02_hw

/-! ## (a) The pairing `tr(S Tᵀ)` on `6 × 6̄` and `V(2, 0) ≅ V(0, 2)ᘁ` -/

/-- `⟨v, w⟩ = tr(ψ₂₀(v) ψ₀₂(w)ᵀ) = ∑ Sᵢⱼ Tᵢⱼ`. -/
noncomputable def pairF : irrepRep 2 0 →ₗ[ℂ] irrepRep 0 2 →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun v w => (psi20 v * (psi02 w).transpose).trace)
    (fun v v' w => by simp [Matrix.add_mul, Matrix.trace_add])
    (fun c v w => by simp [Matrix.trace_smul])
    (fun v w w' => by simp [Matrix.mul_add, Matrix.trace_add])
    (fun c v w => by simp [Matrix.trace_smul])

theorem pairF_apply (v : irrepRep 2 0) (w : irrepRep 0 2) :
    pairF v w = (psi20 v * (psi02 w).transpose).trace := rfl

/-- **The pairing is SU(3)-invariant:** `tr(gSgᵀ (ḡTḡᵀ)ᵀ) = tr(S Tᵀ)`. -/
theorem pairF_invariant (g : SU3) (v : irrepRep 2 0) (w : irrepRep 0 2) :
    pairF ((irrepRep 2 0).ρ g v) ((irrepRep 0 2).ρ g w) = pairF v w := by
  rw [pairF_apply, pairF_apply, psi20_rho, psi02_rho]
  have : (hb g * psi02 w * (hb g).transpose).transpose =
      hb g * (psi02 w).transpose * (hb g).transpose := by
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [this, trace_conj2 _ _ _ _ (gT_hb g) (hbT_g g)]

theorem trace_mul_FT (S : Mat3) (i j : Fin 3) :
    (S * (F i j).transpose).trace = S i j + S j i := by
  fin_cases i <;> fin_cases j <;>
    simp [F, Matrix.trace, Fin.sum_univ_three, Matrix.mul_apply, Matrix.single_apply] <;> ring

/-- The pairing is nondegenerate on the symmetric matrices. -/
theorem sym_nondeg {S : Mat3} (hS : S ∈ symSub)
    (h : ∀ T ∈ symSub, (S * T.transpose).trace = 0) : S = 0 := by
  rw [mem_symSub] at hS
  ext i j
  have h1 := h (F i j) (F_mem i j)
  rw [trace_mul_FT] at h1
  have h2 : S j i = S i j := by have := congrFun (congrFun hS i) j; simpa using this
  rw [h2] at h1
  have : (2 : ℂ) * S i j = 0 := by linear_combination h1
  simpa using this

/-- An FDRep morphism from an equivariant linear map. -/
noncomputable def homOf {X Y : FDRep ℂ SU3} (f : X →ₗ[ℂ] Y)
    (h : ∀ g x, f (X.ρ g x) = Y.ρ g (f x)) : X ⟶ Y :=
  ⟨InducedCategory.homMk (ModuleCat.ofHom f), fun g => by ext x; exact h g x⟩

theorem homOf_apply {X Y : FDRep ℂ SU3} (f : X →ₗ[ℂ] Y)
    (h : ∀ g x, f (X.ρ g x) = Y.ρ g (f x)) (x : X) : (homOf f h).hom.hom.hom x = f x := rfl

/-- `κ : V(2, 0) → V(0, 2)ᘁ`, `v ↦ ⟨v, ·⟩`. -/
noncomputable def kappaL : irrepRep 2 0 →ₗ[ℂ] ((irrepRep 0 2)ᘁ : FDRep ℂ SU3) := pairF

theorem rho_mul_inv (X : FDRep ℂ SU3) (g : SU3) (w : X) : X.ρ g (X.ρ g⁻¹ w) = w := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem kappaL_equivariant (g : SU3) (v : irrepRep 2 0) :
    kappaL ((irrepRep 2 0).ρ g v) = ((irrepRep 0 2)ᘁ).ρ g (kappaL v) := by
  refine LinearMap.ext fun (w : irrepRep 0 2) => ?_
  refine Eq.trans ?_ (dual_ρ_apply (irrepRep 0 2) g (pairF v) w).symm
  change pairF ((irrepRep 2 0).ρ g v) w = pairF v ((irrepRep 0 2).ρ g⁻¹ w)
  rw [← pairF_invariant g v ((irrepRep 0 2).ρ g⁻¹ w), rho_mul_inv]

/-- `κ` as a morphism of representations. -/
noncomputable def kappa : irrepRep 2 0 ⟶ (irrepRep 0 2)ᘁ := homOf kappaL kappaL_equivariant

theorem kappaL_injective : Function.Injective kappaL := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have h : ∀ w, pairF v w = 0 := fun w => by
    have := congrArg (fun ℓ : ((irrepRep 0 2)ᘁ : FDRep ℂ SU3) =>
      (show Module.Dual ℂ (irrepRep 0 2) from ℓ) w) hv
    exact this
  have hS : psi20 v = 0 := sym_nondeg (psi20_mem v) (fun T hT => by
    obtain ⟨w, rfl⟩ := exists_psi02 hT
    exact h w)
  exact psi20_injective (hS.trans (map_zero psi20).symm)

theorem kappa_bijective : Function.Bijective kappa.hom.hom.hom := by
  refine ⟨kappaL_injective, ?_⟩
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 kappaL_injective
  change Module.finrank ℂ (irrepRep 2 0) = Module.finrank ℂ (Module.Dual ℂ (irrepRep 0 2))
  rw [Subspace.dual_finrank_eq, finrank_irrepRep20, finrank_irrepRep02]

/-- **`V(2, 0) ≅ V(0, 2)ᘁ`** (`6 ≅ 6̄ᘁ`), from the nondegenerate invariant pairing. -/
noncomputable def conj20 : irrepRep 2 0 ≅ (irrepRep 0 2)ᘁ :=
  haveI := isIso_of_bijective kappa kappa_bijective
  asIso kappa

/-- **`V(0, 2) ≅ V(2, 0)ᘁ`** (`6̄ ≅ 6ᘁ`). -/
noncomputable def conj02 : irrepRep 0 2 ≅ (irrepRep 2 0)ᘁ :=
  ddIso _ ≪≫ dualIso conj20.symm

/-- `tr(S Tᵀ)` on `6 × 6̄`, times the scalar of a trivial third slot. -/
noncomputable def pairForm :
    irrepRep 2 0 →ₗ[ℂ] irrepRep 0 2 →ₗ[ℂ] (𝟙_ (FDRep ℂ SU3) : FDRep ℂ SU3) →ₗ[ℂ] ℂ :=
  mk3 (fun v w c => (show ℂ from c) * pairF v w)
    (fun x x' y z => by simp [mul_add])
    (fun c x y z => by simp; ring)
    (fun x y y' z => by simp [mul_add])
    (fun c x y z => by simp; ring)
    (fun x y z z' => add_mul _ _ _)
    (fun c x y z => mul_assoc _ _ _)

theorem pairForm_invariant (g : SU3) (v : irrepRep 2 0) (w : irrepRep 0 2)
    (c : (𝟙_ (FDRep ℂ SU3) : FDRep ℂ SU3)) :
    pairForm ((irrepRep 2 0).ρ g v) ((irrepRep 0 2).ρ g w) ((𝟙_ (FDRep ℂ SU3)).ρ g c) =
      pairForm v w c := by
  change (show ℂ from c) * pairF ((irrepRep 2 0).ρ g v) ((irrepRep 0 2).ρ g w) = _
  rw [pairF_invariant]
  rfl

/-- **The pairing is nonzero:** `tr(E₀₀ E₀₀ᵀ) = 1`. -/
theorem pairForm_witness : ∃ v w, pairForm v w (1 : ℂ) = 1 := by
  obtain ⟨v, hv⟩ := exists_psi20 (E_mem 0)
  obtain ⟨w, hw⟩ := exists_psi02 (E_mem 0)
  refine ⟨v, w, ?_⟩
  change (1 : ℂ) * pairF v w = 1
  rw [one_mul, pairF_apply, hv, hw]
  simp [Matrix.trace, Fin.sum_univ_three, Matrix.mul_apply, Matrix.single_apply]

/-! ## (b) `φᵀ S χ` on `6 × 3̄ × 3̄` and `xᵀ T y` on `6̄ × 3 × 3` -/

/-- `tr(S · cv(χ) cv(φ)ᵀ) = cv(φ)ᵀ S cv(χ)` on `6 × 3̄ × 3̄`. -/
noncomputable def symAntiForm : irrepRep 2 0 →ₗ[ℂ] antifund →ₗ[ℂ] antifund →ₗ[ℂ] ℂ :=
  mk3 (fun v φ χ => (psi20 v * outerA χ φ).trace)
    (fun x x' y z => by simp [Matrix.add_mul, Matrix.trace_add])
    (fun c x y z => by simp [Matrix.trace_smul])
    (fun x y y' z => by simp [Matrix.mul_add, Matrix.trace_add])
    (fun c x y z => by simp [Matrix.trace_smul])
    (fun x y z z' => by simp [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add])
    (fun c x y z => by simp [Matrix.trace_smul])

theorem symAntiForm_invariant (g : SU3) (v : irrepRep 2 0) (φ χ : antifund) :
    symAntiForm ((irrepRep 2 0).ρ g v) (antifund.ρ g φ) (antifund.ρ g χ) = symAntiForm v φ χ := by
  change (psi20 ((irrepRep 2 0).ρ g v) * outerA (antifund.ρ g χ) (antifund.ρ g φ)).trace =
    (psi20 v * outerA χ φ).trace
  rw [psi20_rho, outerA_rho, trace_conj2 _ _ _ _ (gT_hb g) (hbT_g g)]

theorem symAntiForm_witness : symAntiForm (hwIrrep 2 0) (evd 0) (evd 0) = 1 := by
  change (psi20 (hwIrrep 2 0) * outerA (evd 0) (evd 0)).trace = 1
  rw [psi20_hw, outerA_evd]
  simp [Matrix.trace, Fin.sum_univ_three, Matrix.mul_apply, Matrix.single_apply]

/-- `tr(T · y xᵀ) = xᵀ T y` on `6̄ × 3 × 3`. -/
noncomputable def symFundForm : irrepRep 0 2 →ₗ[ℂ] fund →ₗ[ℂ] fund →ₗ[ℂ] ℂ :=
  mk3 (fun w x y => (psi02 w * outerF y x).trace)
    (fun x x' y z => by simp [Matrix.add_mul, Matrix.trace_add])
    (fun c x y z => by simp [Matrix.trace_smul])
    (fun x y y' z => by simp [Matrix.mul_add, Matrix.trace_add])
    (fun c x y z => by simp [Matrix.trace_smul])
    (fun x y z z' => by simp [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add])
    (fun c x y z => by simp [Matrix.trace_smul])

theorem symFundForm_invariant (g : SU3) (w : irrepRep 0 2) (x y : fund) :
    symFundForm ((irrepRep 0 2).ρ g w) (fund.ρ g x) (fund.ρ g y) = symFundForm w x y := by
  change (psi02 ((irrepRep 0 2).ρ g w) * outerF (fund.ρ g y) (fund.ρ g x)).trace =
    (psi02 w * outerF y x).trace
  rw [psi02_rho, outerF_rho, trace_conj2 _ _ _ _ (hbT_g g) (gT_hb g)]

theorem symFundForm_witness : symFundForm (hwIrrep 0 2) (ev 2) (ev 2) = 1 := by
  change (psi02 (hwIrrep 0 2) * outerF (ev 2) (ev 2)).trace = 1
  rw [psi02_hw, outerF_ev]
  simp [Matrix.trace, Fin.sum_univ_three, Matrix.mul_apply, Matrix.single_apply]

/-! ## (c) `ε(S Xᵀ, x)` on `6 × 3 × 8` and `ε(T X, cv φ)` on `6̄ × 3̄ × 8` -/

theorem ad_transpose (g : SU3) (X : Mat3) :
    (g.1 * X * star g.1).transpose = hb g * X.transpose * g.1.transpose := by
  simp [hb, Matrix.transpose_mul, Matrix.mul_assoc]

/-- `ε_{ijk} (S Xᵀ)_{ij} x_k` on `6 × 3 × 8`. -/
noncomputable def sym38Form : irrepRep 2 0 →ₗ[ℂ] fund →ₗ[ℂ] irrepRep 1 1 →ₗ[ℂ] ℂ :=
  mk3 (fun v x X => epsC (psi20 v * (psi X).transpose) (show Fin 3 → ℂ from x))
    (fun x x' y z => by simp only [map_add, Matrix.add_mul]; exact epsC_add_left _ _ _)
    (fun c x y z => by simp only [map_smul, Matrix.smul_mul]; exact epsC_smul_left _ _ _)
    (fun x y y' z => epsC_add_right _ _ _)
    (fun c x y z => epsC_smul_right _ _ _)
    (fun x y z z' => by
      simp only [map_add, Matrix.transpose_add, Matrix.mul_add]; exact epsC_add_left _ _ _)
    (fun c x y z => by
      simp only [map_smul, Matrix.transpose_smul, Matrix.mul_smul]; exact epsC_smul_left _ _ _)

theorem sym38Form_invariant (g : SU3) (v : irrepRep 2 0) (x : fund) (X : irrepRep 1 1) :
    sym38Form ((irrepRep 2 0).ρ g v) (fund.ρ g x) ((irrepRep 1 1).ρ g X) = sym38Form v x X := by
  change epsC (psi20 ((irrepRep 2 0).ρ g v) * (psi ((irrepRep 1 1).ρ g X)).transpose)
      (g.1.mulVec (show Fin 3 → ℂ from x)) = epsC (psi20 v * (psi X).transpose) x
  rw [psi20_rho, psi_equivariant, ad_transpose]
  have : g.1 * psi20 v * g.1.transpose * (hb g * (psi X).transpose * g.1.transpose) =
      g.1 * (psi20 v * (psi X).transpose) * g.1.transpose := by
    calc g.1 * psi20 v * g.1.transpose * (hb g * (psi X).transpose * g.1.transpose)
        = g.1 * psi20 v * (g.1.transpose * hb g) * (psi X).transpose * g.1.transpose := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [gT_hb, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [this, epsC_conj, det_eq_one, one_mul]

theorem sym38Form_witness : ∃ X : irrepRep 1 1, sym38Form (hwIrrep 2 0) (ev 2) X = 1 := by
  obtain ⟨X, hX⟩ := exists_psi (E 1 0) (by simp [Matrix.trace])
  refine ⟨X, ?_⟩
  change epsC (psi20 (hwIrrep 2 0) * (psi X).transpose) (Pi.single 2 1) = 1
  rw [psi20_hw, hX]
  simp [epsC, eps, Fin.sum_univ_three, Matrix.mul_apply, Matrix.single_apply]

/-- `ε^{ijk} (T X)_{ij} φ_k` on `6̄ × 3̄ × 8`. -/
noncomputable def sym3b8Form : irrepRep 0 2 →ₗ[ℂ] antifund →ₗ[ℂ] irrepRep 1 1 →ₗ[ℂ] ℂ :=
  mk3 (fun w φ X => epsC (psi02 w * psi X) (cvL φ))
    (fun x x' y z => by simp only [map_add, Matrix.add_mul, epsC_add_left])
    (fun c x y z => by simp only [map_smul, Matrix.smul_mul, epsC_smul_left])
    (fun x y y' z => by simp only [map_add, epsC_add_right])
    (fun c x y z => by simp only [map_smul, epsC_smul_right])
    (fun x y z z' => by simp only [map_add, Matrix.mul_add, epsC_add_left])
    (fun c x y z => by simp only [map_smul, Matrix.mul_smul, epsC_smul_left])

theorem sym3b8Form_invariant (g : SU3) (w : irrepRep 0 2) (φ : antifund) (X : irrepRep 1 1) :
    sym3b8Form ((irrepRep 0 2).ρ g w) (antifund.ρ g φ) ((irrepRep 1 1).ρ g X) =
      sym3b8Form w φ X := by
  change epsC (psi02 ((irrepRep 0 2).ρ g w) * psi ((irrepRep 1 1).ρ g X)) (cvL (antifund.ρ g φ)) =
    epsC (psi02 w * psi X) (cvL φ)
  rw [psi02_rho, psi_equivariant, cvL_rho]
  have : hb g * psi02 w * (hb g).transpose * (g.1 * psi X * star g.1) =
      hb g * (psi02 w * psi X) * (hb g).transpose := by
    calc hb g * psi02 w * (hb g).transpose * (g.1 * psi X * star g.1)
        = hb g * psi02 w * ((hb g).transpose * g.1) * psi X * star g.1 := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hbT_g, Matrix.mul_one, ← hbT g]; simp only [Matrix.mul_assoc]
  rw [this, epsC_conj, det_hb, one_mul]

theorem sym3b8Form_witness : ∃ X : irrepRep 1 1, sym3b8Form (hwIrrep 0 2) (evd 1) X = 1 := by
  obtain ⟨X, hX⟩ := exists_psi (E 2 0) (by simp [Matrix.trace])
  refine ⟨X, ?_⟩
  change epsC (psi02 (hwIrrep 0 2) * psi X) (cvL (evd 1)) = 1
  rw [psi02_hw, hX, cvL_evd]
  simp [epsC, eps, Fin.sum_univ_three, Matrix.mul_apply, Matrix.single_apply]


/-! ## Incoming theta vertices from the forms -/

theorem pairForm_ne : ∃ v w, pairForm v w (1 : ℂ) ≠ 0 := by
  obtain ⟨v, w, h⟩ := pairForm_witness
  exact ⟨v, w, by rw [h]; exact one_ne_zero⟩

/-- Incoming vertex `(1, 6̄, 6)`, by `tr(S Tᵀ)`. -/
theorem in_1_6b_6 :
    Representation.invariants (thetaVertex false (irrepRep 0 0) (irrepRep 0 2) (irrepRep 2 0)).ρ ≠ ⊥ := by
  obtain ⟨v, w, h⟩ := pairForm_ne
  exact invariants_ne_bot_of_iso (thetaVertexIso false irrep00Iso (Iso.refl _) (Iso.refl _))
    (incoming_of_trilinear pairForm pairForm_invariant v w (1 : ℂ) h)

/-- Incoming vertex `(3̄, 3̄, 6)`, by `φᵀ S χ`. -/
theorem in_3b_3b_6 :
    Representation.invariants (thetaVertex false (irrepRep 0 1) (irrepRep 0 1) (irrepRep 2 0)).ρ ≠ ⊥ :=
  invariants_ne_bot_of_iso (thetaVertexIso false irrep01Iso irrep01Iso (Iso.refl _))
    (incoming_of_trilinear symAntiForm symAntiForm_invariant _ _ _
      (by rw [symAntiForm_witness]; exact one_ne_zero))

/-- Incoming vertex `(3, 3, 6̄)`, by `xᵀ T y`. -/
theorem in_3_3_6b :
    Representation.invariants (thetaVertex false (irrepRep 1 0) (irrepRep 1 0) (irrepRep 0 2)).ρ ≠ ⊥ :=
  invariants_ne_bot_of_iso (thetaVertexIso false irrep10Iso irrep10Iso (Iso.refl _))
    (incoming_of_trilinear symFundForm symFundForm_invariant _ _ _
      (by rw [symFundForm_witness]; exact one_ne_zero))

/-- Incoming vertex `(8, 3, 6)`, by `ε(S Xᵀ, x)`. -/
theorem in_8_3_6 :
    Representation.invariants (thetaVertex false (irrepRep 1 1) (irrepRep 1 0) (irrepRep 2 0)).ρ ≠ ⊥ := by
  obtain ⟨X, h⟩ := sym38Form_witness
  exact invariants_ne_bot_of_iso (thetaVertexIso false (Iso.refl _) irrep10Iso (Iso.refl _))
    (incoming_of_trilinear sym38Form sym38Form_invariant _ _ X (by rw [h]; exact one_ne_zero))

/-- Incoming vertex `(8, 3̄, 6̄)`, by `ε(T X, cv φ)`. -/
theorem in_8_3b_6b :
    Representation.invariants (thetaVertex false (irrepRep 1 1) (irrepRep 0 1) (irrepRep 0 2)).ρ ≠ ⊥ := by
  obtain ⟨X, h⟩ := sym3b8Form_witness
  exact invariants_ne_bot_of_iso (thetaVertexIso false (Iso.refl _) irrep01Iso (Iso.refl _))
    (incoming_of_trilinear sym3b8Form sym3b8Form_invariant _ _ X (by rw [h]; exact one_ne_zero))

theorem in_6b_1_6 :
    Representation.invariants (thetaVertex false (irrepRep 0 2) (irrepRep 0 0) (irrepRep 2 0)).ρ ≠ ⊥ :=
  perm12 in_1_6b_6

theorem in_6b_6_1 :
    Representation.invariants (thetaVertex false (irrepRep 0 2) (irrepRep 2 0) (irrepRep 0 0)).ρ ≠ ⊥ :=
  perm23 in_6b_1_6

theorem in_1_6_6b :
    Representation.invariants (thetaVertex false (irrepRep 0 0) (irrepRep 2 0) (irrepRep 0 2)).ρ ≠ ⊥ :=
  perm23 in_1_6b_6

theorem in_6_1_6b :
    Representation.invariants (thetaVertex false (irrepRep 2 0) (irrepRep 0 0) (irrepRep 0 2)).ρ ≠ ⊥ :=
  perm12 in_1_6_6b

theorem in_6_6b_1 :
    Representation.invariants (thetaVertex false (irrepRep 2 0) (irrepRep 0 2) (irrepRep 0 0)).ρ ≠ ⊥ :=
  perm23 in_6_1_6b

theorem in_3b_6_3b :
    Representation.invariants (thetaVertex false (irrepRep 0 1) (irrepRep 2 0) (irrepRep 0 1)).ρ ≠ ⊥ :=
  perm23 in_3b_3b_6

theorem in_6_3b_3b :
    Representation.invariants (thetaVertex false (irrepRep 2 0) (irrepRep 0 1) (irrepRep 0 1)).ρ ≠ ⊥ :=
  perm12 in_3b_6_3b

theorem in_3_6b_3 :
    Representation.invariants (thetaVertex false (irrepRep 1 0) (irrepRep 0 2) (irrepRep 1 0)).ρ ≠ ⊥ :=
  perm23 in_3_3_6b

theorem in_6b_3_3 :
    Representation.invariants (thetaVertex false (irrepRep 0 2) (irrepRep 1 0) (irrepRep 1 0)).ρ ≠ ⊥ :=
  perm12 in_3_6b_3

theorem in_8_6_3 :
    Representation.invariants (thetaVertex false (irrepRep 1 1) (irrepRep 2 0) (irrepRep 1 0)).ρ ≠ ⊥ :=
  perm23 in_8_3_6

theorem in_6_8_3 :
    Representation.invariants (thetaVertex false (irrepRep 2 0) (irrepRep 1 1) (irrepRep 1 0)).ρ ≠ ⊥ :=
  perm12 in_8_6_3

theorem in_6_3_8 :
    Representation.invariants (thetaVertex false (irrepRep 2 0) (irrepRep 1 0) (irrepRep 1 1)).ρ ≠ ⊥ :=
  perm23 in_6_8_3

theorem in_8_6b_3b :
    Representation.invariants (thetaVertex false (irrepRep 1 1) (irrepRep 0 2) (irrepRep 0 1)).ρ ≠ ⊥ :=
  perm23 in_8_3b_6b

theorem in_6b_8_3b :
    Representation.invariants (thetaVertex false (irrepRep 0 2) (irrepRep 1 1) (irrepRep 0 1)).ρ ≠ ⊥ :=
  perm12 in_8_6b_3b

theorem in_6b_3b_8 :
    Representation.invariants (thetaVertex false (irrepRep 0 2) (irrepRep 0 1) (irrepRep 1 1)).ρ ≠ ⊥ :=
  perm23 in_6b_8_3b


/-! ## The sextet rows of the theta table -/

/-- Row `(3b, 3b, 6)`. -/
theorem row_3bar_3bar_6 : ((0, 1), (0, 1), (2, 0)) ∈ thetaList ∧
    Representation.invariants (thetaVertex true (irrepRep 0 1) (irrepRep 0 1) (irrepRep 2 0)).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false (irrepRep 0 1) (irrepRep 0 1) (irrepRep 2 0)).ρ ≠ ⊥ := by
  exact ⟨by decide, outgoing_of_incoming conj01 conj01 conj20 in_3_3_6b, in_3b_3b_6⟩

/-- Row `(3b, 6, 3b)`. -/
theorem row_3bar_6_3bar : ((0, 1), (2, 0), (0, 1)) ∈ thetaList ∧
    Representation.invariants (thetaVertex true (irrepRep 0 1) (irrepRep 2 0) (irrepRep 0 1)).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false (irrepRep 0 1) (irrepRep 2 0) (irrepRep 0 1)).ρ ≠ ⊥ := by
  exact ⟨by decide, outgoing_of_incoming conj01 conj20 conj01 in_3_6b_3, in_3b_6_3b⟩

/-- Row `(6b, 1, 6)`. -/
theorem row_6bar_1_6 : ((0, 2), (0, 0), (2, 0)) ∈ thetaList ∧
    Representation.invariants (thetaVertex true (irrepRep 0 2) (irrepRep 0 0) (irrepRep 2 0)).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false (irrepRep 0 2) (irrepRep 0 0) (irrepRep 2 0)).ρ ≠ ⊥ := by
  exact ⟨by decide, outgoing_of_incoming conj02 conj00 conj20 in_6_1_6b, in_6b_1_6⟩

/-- Row `(6b, 3b, 8)`. -/
theorem row_6bar_3bar_8 : ((0, 2), (0, 1), (1, 1)) ∈ thetaList ∧
    Representation.invariants (thetaVertex true (irrepRep 0 2) (irrepRep 0 1) (irrepRep 1 1)).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false (irrepRep 0 2) (irrepRep 0 1) (irrepRep 1 1)).ρ ≠ ⊥ := by
  obtain ⟨c8⟩ := irrep11_self_dual
  exact ⟨by decide, outgoing_of_incoming conj02 conj01 c8 in_6_3_8, in_6b_3b_8⟩

/-- Row `(6b, 3, 3)`. -/
theorem row_6bar_3_3 : ((0, 2), (1, 0), (1, 0)) ∈ thetaList ∧
    Representation.invariants (thetaVertex true (irrepRep 0 2) (irrepRep 1 0) (irrepRep 1 0)).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false (irrepRep 0 2) (irrepRep 1 0) (irrepRep 1 0)).ρ ≠ ⊥ := by
  exact ⟨by decide, outgoing_of_incoming conj02 conj10 conj10 in_6_3b_3b, in_6b_3_3⟩

/-- Row `(6b, 8, 3b)`. -/
theorem row_6bar_8_3bar : ((0, 2), (1, 1), (0, 1)) ∈ thetaList ∧
    Representation.invariants (thetaVertex true (irrepRep 0 2) (irrepRep 1 1) (irrepRep 0 1)).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false (irrepRep 0 2) (irrepRep 1 1) (irrepRep 0 1)).ρ ≠ ⊥ := by
  obtain ⟨c8⟩ := irrep11_self_dual
  exact ⟨by decide, outgoing_of_incoming conj02 c8 conj01 in_6_8_3, in_6b_8_3b⟩

/-- Row `(6b, 6, 1)`. -/
theorem row_6bar_6_1 : ((0, 2), (2, 0), (0, 0)) ∈ thetaList ∧
    Representation.invariants (thetaVertex true (irrepRep 0 2) (irrepRep 2 0) (irrepRep 0 0)).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false (irrepRep 0 2) (irrepRep 2 0) (irrepRep 0 0)).ρ ≠ ⊥ := by
  exact ⟨by decide, outgoing_of_incoming conj02 conj20 conj00 in_6_6b_1, in_6b_6_1⟩

/-- Row `(3, 6b, 3)`. -/
theorem row_3_6bar_3 : ((1, 0), (0, 2), (1, 0)) ∈ thetaList ∧
    Representation.invariants (thetaVertex true (irrepRep 1 0) (irrepRep 0 2) (irrepRep 1 0)).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false (irrepRep 1 0) (irrepRep 0 2) (irrepRep 1 0)).ρ ≠ ⊥ := by
  exact ⟨by decide, outgoing_of_incoming conj10 conj02 conj10 in_3b_6_3b, in_3_6b_3⟩

/-- Row `(3, 3, 6b)`. -/
theorem row_3_3_6bar : ((1, 0), (1, 0), (0, 2)) ∈ thetaList ∧
    Representation.invariants (thetaVertex true (irrepRep 1 0) (irrepRep 1 0) (irrepRep 0 2)).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false (irrepRep 1 0) (irrepRep 1 0) (irrepRep 0 2)).ρ ≠ ⊥ := by
  exact ⟨by decide, outgoing_of_incoming conj10 conj10 conj02 in_3b_3b_6, in_3_3_6b⟩

/-- Row `(8, 3b, 6b)`. -/
theorem row_8_3bar_6bar : ((1, 1), (0, 1), (0, 2)) ∈ thetaList ∧
    Representation.invariants (thetaVertex true (irrepRep 1 1) (irrepRep 0 1) (irrepRep 0 2)).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false (irrepRep 1 1) (irrepRep 0 1) (irrepRep 0 2)).ρ ≠ ⊥ := by
  obtain ⟨c8⟩ := irrep11_self_dual
  exact ⟨by decide, outgoing_of_incoming c8 conj01 conj02 in_8_3_6, in_8_3b_6b⟩

/-- Row `(8, 6b, 3b)`. -/
theorem row_8_6bar_3bar : ((1, 1), (0, 2), (0, 1)) ∈ thetaList ∧
    Representation.invariants (thetaVertex true (irrepRep 1 1) (irrepRep 0 2) (irrepRep 0 1)).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false (irrepRep 1 1) (irrepRep 0 2) (irrepRep 0 1)).ρ ≠ ⊥ := by
  obtain ⟨c8⟩ := irrep11_self_dual
  exact ⟨by decide, outgoing_of_incoming c8 conj02 conj01 in_8_6_3, in_8_6b_3b⟩

/-- Row `(8, 3, 6)`. -/
theorem row_8_3_6 : ((1, 1), (1, 0), (2, 0)) ∈ thetaList ∧
    Representation.invariants (thetaVertex true (irrepRep 1 1) (irrepRep 1 0) (irrepRep 2 0)).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false (irrepRep 1 1) (irrepRep 1 0) (irrepRep 2 0)).ρ ≠ ⊥ := by
  obtain ⟨c8⟩ := irrep11_self_dual
  exact ⟨by decide, outgoing_of_incoming c8 conj10 conj20 in_8_3b_6b, in_8_3_6⟩

/-- Row `(8, 6, 3)`. -/
theorem row_8_6_3 : ((1, 1), (2, 0), (1, 0)) ∈ thetaList ∧
    Representation.invariants (thetaVertex true (irrepRep 1 1) (irrepRep 2 0) (irrepRep 1 0)).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false (irrepRep 1 1) (irrepRep 2 0) (irrepRep 1 0)).ρ ≠ ⊥ := by
  obtain ⟨c8⟩ := irrep11_self_dual
  exact ⟨by decide, outgoing_of_incoming c8 conj20 conj10 in_8_6b_3b, in_8_6_3⟩

/-- Row `(6, 1, 6b)`. -/
theorem row_6_1_6bar : ((2, 0), (0, 0), (0, 2)) ∈ thetaList ∧
    Representation.invariants (thetaVertex true (irrepRep 2 0) (irrepRep 0 0) (irrepRep 0 2)).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false (irrepRep 2 0) (irrepRep 0 0) (irrepRep 0 2)).ρ ≠ ⊥ := by
  exact ⟨by decide, outgoing_of_incoming conj20 conj00 conj02 in_6b_1_6, in_6_1_6b⟩

/-- Row `(6, 3b, 3b)`. -/
theorem row_6_3bar_3bar : ((2, 0), (0, 1), (0, 1)) ∈ thetaList ∧
    Representation.invariants (thetaVertex true (irrepRep 2 0) (irrepRep 0 1) (irrepRep 0 1)).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false (irrepRep 2 0) (irrepRep 0 1) (irrepRep 0 1)).ρ ≠ ⊥ := by
  exact ⟨by decide, outgoing_of_incoming conj20 conj01 conj01 in_6b_3_3, in_6_3b_3b⟩

/-- Row `(6, 6b, 1)`. -/
theorem row_6_6bar_1 : ((2, 0), (0, 2), (0, 0)) ∈ thetaList ∧
    Representation.invariants (thetaVertex true (irrepRep 2 0) (irrepRep 0 2) (irrepRep 0 0)).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false (irrepRep 2 0) (irrepRep 0 2) (irrepRep 0 0)).ρ ≠ ⊥ := by
  exact ⟨by decide, outgoing_of_incoming conj20 conj02 conj00 in_6b_6_1, in_6_6b_1⟩

/-- Row `(6, 3, 8)`. -/
theorem row_6_3_8 : ((2, 0), (1, 0), (1, 1)) ∈ thetaList ∧
    Representation.invariants (thetaVertex true (irrepRep 2 0) (irrepRep 1 0) (irrepRep 1 1)).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false (irrepRep 2 0) (irrepRep 1 0) (irrepRep 1 1)).ρ ≠ ⊥ := by
  obtain ⟨c8⟩ := irrep11_self_dual
  exact ⟨by decide, outgoing_of_incoming conj20 conj10 c8 in_6b_3b_8, in_6_3_8⟩

/-- Row `(6, 8, 3)`. -/
theorem row_6_8_3 : ((2, 0), (1, 1), (1, 0)) ∈ thetaList ∧
    Representation.invariants (thetaVertex true (irrepRep 2 0) (irrepRep 1 1) (irrepRep 1 0)).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false (irrepRep 2 0) (irrepRep 1 1) (irrepRep 1 0)).ρ ≠ ⊥ := by
  obtain ⟨c8⟩ := irrep11_self_dual
  exact ⟨by decide, outgoing_of_incoming conj20 c8 conj10 in_6b_8_3b, in_6_8_3⟩


/-- The eighteen rows of the theta table with a sextet arm (`6 = V(2, 0)` or `6̄ = V(0, 2)`). -/
def symRows : List (Irrep × Irrep × Irrep) :=
  [((0, 1), (0, 1), (2, 0)), ((0, 1), (2, 0), (0, 1)), ((0, 2), (0, 0), (2, 0)), ((0, 2), (0, 1), (1, 1)), ((0, 2), (1, 0), (1, 0)), ((0, 2), (1, 1), (0, 1)), ((0, 2), (2, 0), (0, 0)), ((1, 0), (0, 2), (1, 0)), ((1, 0), (1, 0), (0, 2)), ((1, 1), (0, 1), (0, 2)), ((1, 1), (0, 2), (0, 1)), ((1, 1), (1, 0), (2, 0)), ((1, 1), (2, 0), (1, 0)), ((2, 0), (0, 0), (0, 2)), ((2, 0), (0, 1), (0, 1)), ((2, 0), (0, 2), (0, 0)), ((2, 0), (1, 0), (1, 1)), ((2, 0), (1, 1), (1, 0))]

theorem symRows_length : symRows.length = 18 := rfl

/-- **`symRows` are exactly the rows of `thetaList` with a `6` or `6̄` arm.** -/
theorem symRows_iff (t : Irrep × Irrep × Irrep) :
    t ∈ symRows ↔ t ∈ thetaList ∧ (t.1 = (2, 0) ∨ t.1 = (0, 2) ∨ t.2.1 = (2, 0) ∨
      t.2.1 = (0, 2) ∨ t.2.2 = (2, 0) ∨ t.2.2 = (0, 2)) := by
  have h1 : ∀ t ∈ symRows, t ∈ thetaList ∧ (t.1 = (2, 0) ∨ t.1 = (0, 2) ∨ t.2.1 = (2, 0) ∨
      t.2.1 = (0, 2) ∨ t.2.2 = (2, 0) ∨ t.2.2 = (0, 2)) := by decide
  have h2 : ∀ t ∈ thetaList, (t.1 = (2, 0) ∨ t.1 = (0, 2) ∨ t.2.1 = (2, 0) ∨
      t.2.1 = (0, 2) ∨ t.2.2 = (2, 0) ∨ t.2.2 = (0, 2)) → t ∈ symRows := by decide
  exact ⟨fun h => h1 t h, fun ⟨h, h'⟩ => h2 t h h'⟩

/-- **The eighteen sextet rows are attained on the `V(p, q)` arms:** each is in the theta table
and both theta vertices have a nonzero invariant. -/
theorem symRows_irrep_both (t : Irrep × Irrep × Irrep) (ht : t ∈ symRows) :
    t ∈ thetaList ∧
    Representation.invariants (thetaVertex true (irrepRep t.1.1 t.1.2)
      (irrepRep t.2.1.1 t.2.1.2) (irrepRep t.2.2.1 t.2.2.2)).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false (irrepRep t.1.1 t.1.2)
      (irrepRep t.2.1.1 t.2.1.2) (irrepRep t.2.2.1 t.2.2.2)).ρ ≠ ⊥ := by
  simp only [symRows, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

  · exact row_3bar_3bar_6

  · exact row_3bar_6_3bar

  · exact row_6bar_1_6

  · exact row_6bar_3bar_8

  · exact row_6bar_3_3

  · exact row_6bar_8_3bar

  · exact row_6bar_6_1

  · exact row_3_6bar_3

  · exact row_3_3_6bar

  · exact row_8_3bar_6bar

  · exact row_8_6bar_3bar

  · exact row_8_3_6

  · exact row_8_6_3

  · exact row_6_1_6bar

  · exact row_6_3bar_3bar

  · exact row_6_6bar_1

  · exact row_6_3_8

  · exact row_6_8_3


/-- All 34 rows: the sixteen of `allAttainedRows` (arms in `{1, 3, 3̄, 8}`) and the eighteen
sextet rows. -/
def fullRows : List (Irrep × Irrep × Irrep) := allAttainedRows ++ symRows

theorem fullRows_length : fullRows.length = 34 := rfl

/-- **`fullRows` and `thetaList` have the same members.** -/
theorem fullRows_iff (t : Irrep × Irrep × Irrep) : t ∈ fullRows ↔ t ∈ thetaList := by
  have h1 : ∀ t ∈ fullRows, t ∈ thetaList := by decide
  have h2 : ∀ t ∈ thetaList, t ∈ fullRows := by decide
  exact ⟨h1 t, h2 t⟩

/-- **All 34 rows of the theta table are attained on the `V(p, q)` arms:** for every row
`(a, b, c)` of `thetaList`, both theta vertices with arms `V(a)`, `V(b)`, `V(c)` have a nonzero
SU(3)-invariant. -/
theorem thetaList_irrep_both (t : Irrep × Irrep × Irrep) (ht : t ∈ thetaList) :
    Representation.invariants (thetaVertex true (irrepRep t.1.1 t.1.2)
      (irrepRep t.2.1.1 t.2.1.2) (irrepRep t.2.2.1 t.2.2.2)).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false (irrepRep t.1.1 t.1.2)
      (irrepRep t.2.1.1 t.2.1.2) (irrepRep t.2.2.1 t.2.2.2)).ρ ≠ ⊥ := by
  rcases List.mem_append.1 ((fullRows_iff t).2 ht) with h | h
  · exact (allAttainedRows_irrep_both t h).2
  · exact (symRows_irrep_both t h).2

/-- No row of the theta table is left unattained. -/
theorem not_attained_count_zero :
    (thetaList.filter fun t => decide (t ∉ fullRows)).length = 0 := by decide

/-! ## The control: `3 ⊗ 6` has no nonzero invariant

Triality does not decide this one: `ω·I` acts on `3 ⊗ 6` by `ω · ω² = 1`
(`centreActs_fund_sym`). The proof uses three non-central elements instead: the sign matrices
`diag(1, -1, -1)`, `diag(-1, 1, -1)`, the `3-4-5` rotation and the cyclic permutation. -/

/-- `ω·I` acts trivially on `3 ⊗ 6`: the centre gives no obstruction. -/
theorem centreActs_fund_sym : CentreActs zω 1 (fund ⊗ irrepRep 2 0) := by
  have h := centreActs_tensor centreActs_fund (centreCharacter_irrep 2 0)
  have hω : ω * ω ^ triality (2, 0) = 1 := by
    rw [show triality (2, 0) = 2 by decide, ← pow_succ', omega_cube]
  rwa [hω] at h

/-- The `b`-th coordinate slice `x ⊗ w ↦ x_b • w` of `3 ⊗ 6`. -/
noncomputable def coordL (b : Fin 3) : TensorProduct ℂ fund (irrepRep 2 0) →ₗ[ℂ] irrepRep 2 0 :=
  TensorProduct.lift ((LinearMap.lsmul ℂ (irrepRep 2 0)).comp
    (LinearMap.proj b : (Fin 3 → ℂ) →ₗ[ℂ] ℂ))

theorem coordL_tmul (b : Fin 3) (x : fund) (w : irrepRep 2 0) :
    coordL b (x ⊗ₜ[ℂ] w) = (show Fin 3 → ℂ from x) b • w := rfl

theorem coordL_rho (g : SU3) (b : Fin 3) (t : (fund ⊗ irrepRep 2 0 : FDRep ℂ SU3)) :
    coordL b ((fund ⊗ irrepRep 2 0).ρ g t) =
      ∑ a, g.1 b a • (irrepRep 2 0).ρ g (coordL a t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv, smul_add, Finset.sum_add_distrib]
  | tmul x w =>
    rw [tensor_ρ_tmul, coordL_tmul]
    simp only [coordL_tmul, map_smul, smul_smul]
    change (g.1.mulVec (show Fin 3 → ℂ from x)) b • _ = _
    simp only [Matrix.mulVec, dotProduct, Finset.sum_smul]

theorem tmul_decomp (t : (fund ⊗ irrepRep 2 0 : FDRep ℂ SU3)) :
    t = ∑ a, (ev a ⊗ₜ[ℂ] coordL a t : TensorProduct ℂ fund (irrepRep 2 0)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv =>
    conv_lhs => rw [hu, hv]
    simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
  | tmul x w =>
    have hx : x = ∑ a, (show Fin 3 → ℂ from x) a • ev a := by
      change (show Fin 3 → ℂ from x) = ∑ a, (show Fin 3 → ℂ from x) a • (Pi.single a 1 : Fin 3 → ℂ)
      funext k
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
        mul_zero, Fin.sum_univ_three]
      fin_cases k <;> simp
    conv_lhs => rw [hx]
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coordL_tmul]
    exact TensorProduct.smul_tmul _ _ _

theorem zero_of_eq_neg {x : ℂ} (h : x = -x) : x = 0 := by
  have : (2 : ℂ) * x = 0 := by linear_combination h
  simpa using this

/-- A symmetric matrix fixed by `M ↦ -(d M d)` for `d = diag(1, -1, -1)`, `diag(-1, 1, -1)` and by
`M ↦ rot M rotᵀ` is zero. -/
theorem sym_zero_of_signs_rot {M : Mat3} (hM : M ∈ symSub)
    (e1 : M = (-1 : ℂ) • (d1M * M * d1M.transpose))
    (e2 : M = (-1 : ℂ) • (d2M * M * d2M.transpose))
    (e3 : M = rotM * M * rotM.transpose) : M = 0 := by
  rw [mem_symSub] at hM
  have s := fun i j => congrFun (congrFun hM i) j
  have a1 := fun i j => congrFun (congrFun e1 i) j
  have a2 := fun i j => congrFun (congrFun e2 i) j
  have a3 := fun i j => congrFun (congrFun e3 i) j
  have m00 := a1 0 0
  have m11 := a1 1 1
  have m22 := a1 2 2
  have m12 := a1 1 2
  have m02 := a2 0 2
  have r00 := a3 0 0
  have s10 := s 0 1
  have s21 := s 1 2
  have s20 := s 0 2
  simp only [Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply,
    smul_eq_mul] at m00 m11 m22 m12 m02 r00 s10 s21 s20
  simp [d1M, d2M, rotM] at m00 m11 m22 m12 m02 r00
  have h00 := zero_of_eq_neg m00
  have h11 := zero_of_eq_neg m11
  have h22 := zero_of_eq_neg m22
  have h12 := zero_of_eq_neg m12
  have h02 := zero_of_eq_neg m02
  have h01 : M 0 1 = 0 := by
    rw [h00, h11, s10] at r00
    have : (24 / 25 : ℂ) * M 0 1 = 0 := by linear_combination r00
    simpa using this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h11, h22, h12, h02, h01, s10, s21, s20]

/-- **`3 ⊗ 6` has no nonzero invariant** (although triality allows it): the negation of the false
control `SymFundControl`. -/
theorem invariants_fund_sym_eq_bot :
    Representation.invariants (fund ⊗ irrepRep 2 0).ρ = ⊥ := by
  rw [eq_bot_iff]
  intro t ht
  rw [Submodule.mem_bot]
  have key : ∀ (g : SU3) (b : Fin 3),
      coordL b t = ∑ a, g.1 b a • (irrepRep 2 0).ρ g (coordL a t) := fun g b => by
    rw [← coordL_rho, ht g]
  let u : Fin 3 → Mat3 := fun a => psi20 (coordL a t)
  have hu : ∀ (g : SU3) (b : Fin 3), u b = ∑ a, g.1 b a • (g.1 * u a * g.1.transpose) := by
    intro g b
    change psi20 (coordL b t) = _
    rw [key g b]
    simp only [map_sum, map_smul, psi20_rho]
    rfl
  have e1 : u 2 = (-1 : ℂ) • (d1M * u 2 * d1M.transpose) := by
    have := hu d1 2; rw [Fin.sum_univ_three] at this; simpa [d1, d1M] using this
  have e2 : u 2 = (-1 : ℂ) • (d2M * u 2 * d2M.transpose) := by
    have := hu d2 2; rw [Fin.sum_univ_three] at this; simpa [d2, d2M] using this
  have e3 : u 2 = rotM * u 2 * rotM.transpose := by
    have := hu rot 2; rw [Fin.sum_univ_three] at this; simpa [rot, rotM] using this
  have e4 : u 0 = cycMat * u 2 * cycMat.transpose := by
    have := hu cyc 0; rw [Fin.sum_univ_three] at this; simpa [cyc, cycMat] using this
  have e5 : u 1 = cycMat * u 0 * cycMat.transpose := by
    have := hu cyc 1; rw [Fin.sum_univ_three] at this; simpa [cyc, cycMat] using this
  have h2 : u 2 = 0 := sym_zero_of_signs_rot (psi20_mem _) e1 e2 e3
  have h0 : u 0 = 0 := by rw [e4, h2]; simp
  have h1 : u 1 = 0 := by rw [e5, h0]; simp
  have hc : ∀ a, coordL a t = 0 := by
    intro a
    apply psi20_injective
    rw [map_zero]
    fin_cases a
    · exact h0
    · exact h1
    · exact h2
  rw [tmul_decomp t]
  simp [hc]

/-- The same on the arms `V(1, 0) ⊗ V(2, 0)`. -/
theorem invariants_irrep10_irrep20_eq_bot :
    Representation.invariants (irrepRep 1 0 ⊗ irrepRep 2 0).ρ = ⊥ :=
  (invariants_eq_bot_iff_of_iso (irrep10Iso ⊗ᵢ Iso.refl _)).2 invariants_fund_sym_eq_bot

/-- **`6 ⊗ 3` has no nonzero invariant** (braiding). -/
theorem invariants_sym_fund_eq_bot :
    Representation.invariants (irrepRep 2 0 ⊗ fund).ρ = ⊥ :=
  (invariants_eq_bot_iff_of_iso (β_ _ _)).2 invariants_fund_sym_eq_bot

/-- The same on the arms `V(2, 0) ⊗ V(1, 0)`. -/
theorem invariants_irrep20_irrep10_eq_bot :
    Representation.invariants (irrepRep 2 0 ⊗ irrepRep 1 0).ρ = ⊥ :=
  (invariants_eq_bot_iff_of_iso (Iso.refl _ ⊗ᵢ irrep10Iso)).2 invariants_sym_fund_eq_bot

end SymWitnessSU3
