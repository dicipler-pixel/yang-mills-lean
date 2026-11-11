import IrrepIrreducibleSU3

/-!
# Explicit adjoint singlets: the theta rows with an octet arm

Author: Jeromie Beasley (Spectrum · Colour team lead, Grok Bot), with the Team.
ORCID https://orcid.org/0009-0006-4645-5643 · GitHub dicipler-pixel · X @d1c1pler ·
YouTube @AtlasMemoriae · atlas-memoriae.dicipler.workers.dev

`IrrepIrreducibleSU3` identifies `V(1, 1) = irrepRep 1 1` with the traceless matrices through
the equivariant bijection `phi11 : 3 ⊗ 3̄ ⊗ 𝟙 → M₃(ℂ)` (adjoint action `M ↦ g M g⁻¹`). Here
`psi = phi11 ∘ (inclusion)` carries the classical adjoint invariants onto `V(1, 1)`.

**Witnesses (each an SU(3)-invariant, nonzero multilinear form).**
* `trForm`: `tr(XY)` on `8 × 8` (times the scalar of a trivial slot); invariant by
  `tr(gXg⁻¹ gYg⁻¹) = tr(XY)` (`trForm_invariant`), nonzero at `X = E₀₁`, `Y = E₁₀`
  (`trForm_witness`).
* `xiForm`: `ξᵀXη = φ(X x)` on `3 × 3̄ × 8`, a vector, a covector and a matrix
  (`xiForm_invariant`); nonzero at `x = e₀`, `φ = e₁*`, `X = E₁₀` (`xiForm_witness`).
* `fForm`: `tr(X[Y, Z])` on `8 × 8 × 8`, the `f`-type invariant (`fForm_invariant`); nonzero at
  `X = E₀₀ - E₁₁`, `Y = E₀₁`, `Z = E₁₀`, value `2` (`fForm_witness`).
* `dForm`: `tr(X{Y, Z})`, the `d`-type invariant (`dForm_invariant`); nonzero at
  `X = Y = Z = diag(1, 1, -2)`, value `-12` (`dForm_witness`).

**From forms to vertex invariants (no new axioms, Mathlib's rigid structure on `FDRep`).**
An invariant nonzero functional on `X` is a nonzero invariant of `Xᘁ`
(`dual_invariants_ne_bot_of_form`); `(X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ` (`dualTensorIso`, from
`ExactPairing.tensor`), so a trilinear form on `P × Q × R` gives a nonzero invariant at the
incoming theta vertex with arms `(R, Q, P)` (`incoming_of_form`). The braiding permutes arms
(`perm12`, `perm23`). The outgoing vertex of a row is isomorphic to the incoming vertex of its
conjugate row (`outgoing_of_incoming`), using `V(1,0) ≅ V(0,1)ᘁ`, `V(0,1) ≅ V(1,0)ᘁ`,
`V(0,0) ≅ V(0,0)ᘁ` (`conj10`, `conj01`, `conj00`, via `ddIso : X ≅ Xᘁᘁ` and
`dualIsoUnitOfIso`) and the
self-duality of the adjoint `V(1,1) ≅ V(1,1)ᘁ` (`irrep11_self_dual`, from the trace form, the
simplicity of `V(1,1)` and Schur through `iso_of_pair_invariant`).

**Theta rows attained.** The eight rows of `thetaList` with an octet arm and all other arms in
`{1, 3, 3̄}` (`adjointRows_iff`): the six orderings of `(3, 3̄, 8)` (by `ξᵀXη`) and
`(8, 1, 8)`, `(8, 8, 1)` (by `tr(XY)`). For each, both theta vertices with arms `V(a)`, `V(b)`,
`V(c)` have a nonzero invariant (`adjointRows_irrep_both`). Together with the eight rows of
`attainedRows`, **16 of the 34 rows are attained** (`allAttainedRows_irrep_both`,
`allAttainedRows_length`, `allAttainedRows_iff`: exactly the rows whose arms lie in
`{1, 3, 3̄, 8}`). The `(8, 8, 8)` vertex (`row_8_8_8`, by `tr(X[Y, Z])`) is not a table row: its
level `63/3` exceeds `17`.

**Not covered.** The eight rows with an octet arm and a sextet arm (`adjointOpenRows`,
`adjointOpenRows_iff`), and the ten remaining rows with sextet arms only; these need
witnesses on `V(2, 0)`, `V(0, 2)`.

**Control.** `3 ⊗ 8` has no nonzero invariant: `ω·I` acts by `ω · 1 = ω ≠ 1` (triality
`1 + 0 ≢ 0`), `invariants_fund_adjoint_eq_bot`, also on the `V(p, q)` arms
(`invariants_irrep10_irrep11_eq_bot`). `FalseControls/FundAdjointControl.lean` claims a nonzero
invariant and is rejected.

No continuum or mass-gap statement is made.
-/

open CategoryTheory MonoidalCategory CentreCharacterSU3 IrrepEmbedSU3 IrrepSmallIsoSU3
  SingletWitnessSU3 IrrepIrreducibleSU3 GaugeSupport ThetaFloor TrialityVertex

namespace AdjointWitnessSU3

/-! ## Rigid-category tools -/

/-- `(X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ`. -/
noncomputable def dualTensorIso (X Y : FDRep ℂ SU3) : (X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ :=
  rightDualIso (inferInstance : ExactPairing (X ⊗ Y) (X ⊗ Y)ᘁ) ExactPairing.tensor

/-- `X ≅ Xᘁᘁ`. -/
noncomputable def ddIso (X : FDRep ℂ SU3) : X ≅ (Xᘁ : FDRep ℂ SU3)ᘁ :=
  rightDualIso (BraidedCategory.exactPairing_swap X Xᘁ)
    (inferInstance : ExactPairing (Xᘁ : FDRep ℂ SU3) (Xᘁ : FDRep ℂ SU3)ᘁ)

/-- **An invariant nonzero functional on `X` is a nonzero invariant of `Xᘁ`.** -/
theorem dual_invariants_ne_bot_of_form {X : FDRep ℂ SU3} (ℓ : X →ₗ[ℂ] ℂ)
    (hinv : ∀ g x, ℓ (X.ρ g x) = ℓ x) (hne : ℓ ≠ 0) :
    Representation.invariants (Xᘁ).ρ ≠ ⊥ := by
  intro h
  have hv : (show (Xᘁ : FDRep ℂ SU3) from ℓ) ∈ Representation.invariants (Xᘁ).ρ := by
    intro g
    refine LinearMap.ext fun x => ?_
    exact (dual_ρ_apply X g _ x).trans (hinv g⁻¹ x)
  rw [h] at hv
  exact hne ((Submodule.mem_bot ℂ).1 hv)

/-- Swap the first two factors of `X ⊗ (Y ⊗ W)` (braiding). -/
noncomputable def swap12 (X Y W : FDRep ℂ SU3) : X ⊗ (Y ⊗ W) ≅ Y ⊗ (X ⊗ W) :=
  (α_ X Y W).symm ≪≫ whiskerRightIso (β_ X Y) W ≪≫ α_ Y X W

/-- Swapping the first two arms of a theta vertex. -/
theorem perm12 {o : Bool} {A B C : FDRep ℂ SU3}
    (h : Representation.invariants (thetaVertex o A B C).ρ ≠ ⊥) :
    Representation.invariants (thetaVertex o B A C).ρ ≠ ⊥ :=
  invariants_ne_bot_of_iso (swap12 _ _ _) h

/-- Swapping the last two arms of a theta vertex. -/
theorem perm23 {o : Bool} {A B C : FDRep ℂ SU3}
    (h : Representation.invariants (thetaVertex o A B C).ρ ≠ ⊥) :
    Representation.invariants (thetaVertex o A C B).ρ ≠ ⊥ :=
  invariants_ne_bot_of_iso (whiskerLeftIso _ (swap12 _ _ _)) h

/-- **An invariant nonzero functional on `P ⊗ (Q ⊗ R)` gives a nonzero invariant at the
incoming theta vertex with arms `(R, Q, P)`.** -/
theorem incoming_of_form {P Q R : FDRep ℂ SU3} (ℓ : (P ⊗ (Q ⊗ R) : FDRep ℂ SU3) →ₗ[ℂ] ℂ)
    (hinv : ∀ g x, ℓ ((P ⊗ (Q ⊗ R)).ρ g x) = ℓ x) (hne : ℓ ≠ 0) :
    Representation.invariants (thetaVertex false R Q P).ρ ≠ ⊥ := by
  have h := dual_invariants_ne_bot_of_form ℓ hinv hne
  have i : thetaVertex false R Q P ≅ (P ⊗ (Q ⊗ R))ᘁ :=
    (Iso.refl _ : thetaVertex false R Q P ≅ Rᘁ ⊗ (Qᘁ ⊗ (Pᘁ ⊗ 𝟙_ _))) ≪≫
      whiskerLeftIso _ (whiskerLeftIso _ (ρ_ _)) ≪≫ (α_ _ _ _).symm ≪≫
      whiskerRightIso (dualTensorIso Q R).symm _ ≪≫ (dualTensorIso P (Q ⊗ R)).symm
  exact invariants_ne_bot_of_iso i h

/-- The outgoing vertex with arms `(A, B, C)` is isomorphic to the incoming vertex with arms
`(A', B', C')` when `A ≅ A'ᘁ`, `B ≅ B'ᘁ`, `C ≅ C'ᘁ`. -/
theorem outgoing_of_incoming {A B C A' B' C' : FDRep ℂ SU3} (a : A ≅ A'ᘁ) (b : B ≅ B'ᘁ)
    (c : C ≅ C'ᘁ) (h : Representation.invariants (thetaVertex false A' B' C').ρ ≠ ⊥) :
    Representation.invariants (thetaVertex true A B C).ρ ≠ ⊥ :=
  invariants_ne_bot_of_iso ((a ⊗ᵢ (b ⊗ᵢ (c ⊗ᵢ Iso.refl _)) :
    A ⊗ (B ⊗ (C ⊗ 𝟙_ _)) ≅ A'ᘁ ⊗ (B'ᘁ ⊗ (C'ᘁ ⊗ 𝟙_ _)))) h

/-! ## Trilinear forms -/

section mk3
variable {P Q R : Type*} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q]
  [AddCommGroup R] [Module ℂ R]

/-- A trilinear form from a function linear in each slot. -/
noncomputable def mk3 (f : P → Q → R → ℂ)
    (hP : ∀ x x' y z, f (x + x') y z = f x y z + f x' y z)
    (hPs : ∀ (c : ℂ) x y z, f (c • x) y z = c * f x y z)
    (hQ : ∀ x y y' z, f x (y + y') z = f x y z + f x y' z)
    (hQs : ∀ (c : ℂ) x y z, f x (c • y) z = c * f x y z)
    (hR : ∀ x y z z', f x y (z + z') = f x y z + f x y z')
    (hRs : ∀ (c : ℂ) x y z, f x y (c • z) = c * f x y z) :
    P →ₗ[ℂ] Q →ₗ[ℂ] R →ₗ[ℂ] ℂ where
  toFun x := LinearMap.mk₂ ℂ (f x) (hQ x) (fun c y z => hQs c x y z) (hR x)
    (fun c y z => hRs c x y z)
  map_add' x x' := LinearMap.ext fun y => LinearMap.ext fun z => hP x x' y z
  map_smul' c x := LinearMap.ext fun y => LinearMap.ext fun z => hPs c x y z

/-- The functional on `P ⊗ (Q ⊗ R)` of a trilinear form. -/
noncomputable def form3 (F : P →ₗ[ℂ] Q →ₗ[ℂ] R →ₗ[ℂ] ℂ) :
    TensorProduct ℂ P (TensorProduct ℂ Q R) →ₗ[ℂ] ℂ :=
  TensorProduct.lift (TensorProduct.uncurry (RingHom.id ℂ) Q R ℂ ∘ₗ F)

theorem form3_tmul (F : P →ₗ[ℂ] Q →ₗ[ℂ] R →ₗ[ℂ] ℂ) (x : P) (y : Q) (z : R) :
    form3 F (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] z)) = F x y z := rfl

theorem form3_comp (F : P →ₗ[ℂ] Q →ₗ[ℂ] R →ₗ[ℂ] ℂ) (a : P →ₗ[ℂ] P) (b : Q →ₗ[ℂ] Q)
    (c : R →ₗ[ℂ] R) (h : ∀ x y z, F (a x) (b y) (c z) = F x y z) (t) :
    form3 F (TensorProduct.map a (TensorProduct.map b c) t) = form3 F t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => rw [map_add, map_add, hu, hv, map_add]
  | tmul x w =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => rw [TensorProduct.tmul_add, map_add, map_add, hu, hv, map_add]
    | tmul y z =>
      rw [TensorProduct.map_tmul, TensorProduct.map_tmul, form3_tmul, form3_tmul, h]

theorem form3_ne_zero (F : P →ₗ[ℂ] Q →ₗ[ℂ] R →ₗ[ℂ] ℂ) (x : P) (y : Q) (z : R)
    (h : F x y z ≠ 0) : form3 F ≠ 0 := by
  intro h0
  apply h
  rw [← form3_tmul, h0, LinearMap.zero_apply]

end mk3

/-- An SU(3)-invariant trilinear form gives an invariant functional on `P ⊗ (Q ⊗ R)`. -/
theorem form3_invariant {P Q R : FDRep ℂ SU3} (F : P →ₗ[ℂ] Q →ₗ[ℂ] R →ₗ[ℂ] ℂ)
    (h : ∀ g x y z, F (P.ρ g x) (Q.ρ g y) (R.ρ g z) = F x y z) (g : SU3)
    (t : (P ⊗ (Q ⊗ R) : FDRep ℂ SU3)) :
    form3 F ((P ⊗ (Q ⊗ R)).ρ g t) = form3 F t :=
  form3_comp F (P.ρ g) (Q.ρ g) (R.ρ g) (h g) t

/-- An invariant trilinear form, nonzero somewhere, gives a nonzero invariant at the incoming
vertex `(R, Q, P)`. -/
theorem incoming_of_trilinear {P Q R : FDRep ℂ SU3} (F : P →ₗ[ℂ] Q →ₗ[ℂ] R →ₗ[ℂ] ℂ)
    (h : ∀ g x y z, F (P.ρ g x) (Q.ρ g y) (R.ρ g z) = F x y z) (x : P) (y : Q) (z : R)
    (hne : F x y z ≠ 0) :
    Representation.invariants (thetaVertex false R Q P).ρ ≠ ⊥ :=
  incoming_of_form (form3 F) (form3_invariant F h) (form3_ne_zero F x y z hne)

/-! ## The adjoint through `Φ` -/

/-- `ψ : V(1, 1) → M₃(ℂ)`, the restriction of `Φ = phi11`. -/
noncomputable def psi : irrepRep 1 1 →ₗ[ℂ] Mat3 := phi11 ∘ₗ (irrepSub 1 1).subtype

/-- `ψ (g · v) = g ψ(v) g⁻¹`. -/
theorem psi_equivariant (g : SU3) (v : irrepRep 1 1) :
    psi ((irrepRep 1 1).ρ g v) = g.1 * psi v * star g.1 :=
  phi11_equivariant g v.1

/-- `ψ` lands in the traceless matrices. -/
theorem psi_traceless (v : irrepRep 1 1) : (psi v).trace = 0 := by
  have : psi v ∈ tracelessSub := by
    rw [← irrepSub11_map_eq]; exact ⟨v.1, v.2, rfl⟩
  exact this

/-- Every traceless matrix is `ψ` of an element of `V(1, 1)`. -/
theorem exists_psi (M : Mat3) (h : M.trace = 0) : ∃ v : irrepRep 1 1, psi v = M := by
  have hM : M ∈ (irrepSub 1 1).map phi11 := by rw [irrepSub11_map_eq]; exact h
  obtain ⟨t, ht, rfl⟩ := hM
  exact ⟨⟨t, ht⟩, rfl⟩

theorem unitary_left (g : SU3) : star g.1 * g.1 = 1 :=
  (Matrix.mem_unitaryGroup_iff').1 (Matrix.mem_specialUnitaryGroup_iff.1 g.2).1

theorem ad_mul (g : SU3) (A B : Mat3) :
    (g.1 * A * star g.1) * (g.1 * B * star g.1) = g.1 * (A * B) * star g.1 := by
  calc (g.1 * A * star g.1) * (g.1 * B * star g.1)
      = g.1 * A * (star g.1 * g.1) * B * star g.1 := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [unitary_left, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem ad_sub (g : SU3) (A B : Mat3) :
    g.1 * A * star g.1 - g.1 * B * star g.1 = g.1 * (A - B) * star g.1 := by
  rw [Matrix.mul_sub, Matrix.sub_mul]

theorem ad_add (g : SU3) (A B : Mat3) :
    g.1 * A * star g.1 + g.1 * B * star g.1 = g.1 * (A + B) * star g.1 := by
  rw [Matrix.mul_add, Matrix.add_mul]

/-! ## (a) The trace form `tr(XY)` on `8 ⊗ 8` -/

/-- `tr(XY)` on `8 × 8`, times the scalar of a trivial third slot. -/
noncomputable def trForm :
    irrepRep 1 1 →ₗ[ℂ] irrepRep 1 1 →ₗ[ℂ] (𝟙_ (FDRep ℂ SU3) : FDRep ℂ SU3) →ₗ[ℂ] ℂ :=
  mk3 (fun x y c => (show ℂ from c) * (psi x * psi y).trace)
    (fun x x' y z => by simp [Matrix.add_mul, Matrix.trace_add]; ring)
    (fun c x y z => by simp [Matrix.trace_smul]; ring)
    (fun x y y' z => by simp [Matrix.mul_add, Matrix.trace_add]; ring)
    (fun c x y z => by simp [Matrix.trace_smul]; ring)
    (fun x y z z' => add_mul _ _ _)
    (fun c x y z => mul_assoc _ _ _)

theorem trForm_apply (x y : irrepRep 1 1) (c : ℂ) :
    trForm x y c = c * (psi x * psi y).trace := rfl

/-- **`tr(XY)` is SU(3)-invariant:** `tr(gXg⁻¹ gYg⁻¹) = tr(XY)`. -/
theorem trForm_invariant (g : SU3) (x y : irrepRep 1 1) (c : (𝟙_ (FDRep ℂ SU3) : FDRep ℂ SU3)) :
    trForm ((irrepRep 1 1).ρ g x) ((irrepRep 1 1).ρ g y) ((𝟙_ (FDRep ℂ SU3)).ρ g c) =
      trForm x y c := by
  change (show ℂ from c) * (psi ((irrepRep 1 1).ρ g x) * psi ((irrepRep 1 1).ρ g y)).trace = _
  rw [psi_equivariant, psi_equivariant, ad_mul, trace_ad]
  rfl

/-- **`tr(XY)` is nonzero:** `tr(E₀₁ E₁₀) = 1`. -/
theorem trForm_witness : ∃ x y : irrepRep 1 1, trForm x y (1 : ℂ) = 1 := by
  obtain ⟨x, hx⟩ := exists_psi (E 0 1) (by simp [Matrix.trace])
  obtain ⟨y, hy⟩ := exists_psi (E 1 0) (by simp [Matrix.trace])
  refine ⟨x, y, ?_⟩
  rw [trForm_apply, hx, hy, one_mul]
  simp [Matrix.trace]

/-! ## (b) `ξᵀXη` on `3 ⊗ 3̄ ⊗ 8` -/

/-- `ξᵀXη = φ(X x)` on `3 × 3̄ × 8`. -/
noncomputable def xiForm : fund →ₗ[ℂ] antifund →ₗ[ℂ] irrepRep 1 1 →ₗ[ℂ] ℂ :=
  mk3 (fun x φ v => (show Module.Dual ℂ (Fin 3 → ℂ) from φ)
      ((psi v).mulVec (show Fin 3 → ℂ from x)))
    (fun x x' y z => by
      rw [← map_add, ← Matrix.mulVec_add]; rfl)
    (fun c x y z => by
      rw [← smul_eq_mul, ← map_smul, ← Matrix.mulVec_smul]; rfl)
    (fun x y y' z => rfl)
    (fun c x y z => rfl)
    (fun x y z z' => by
      rw [map_add, Matrix.add_mulVec, map_add])
    (fun c x y z => by
      rw [map_smul, Matrix.smul_mulVec, map_smul, smul_eq_mul])

theorem xiForm_apply (x : Fin 3 → ℂ) (φ : Module.Dual ℂ (Fin 3 → ℂ)) (v : irrepRep 1 1) :
    xiForm (show fund from x) (show antifund from φ) v = φ ((psi v).mulVec x) := rfl

/-- **`ξᵀXη` is SU(3)-invariant:** `(g⁻¹ᵀφ)(gXg⁻¹ · g x) = φ(X x)`. -/
theorem xiForm_invariant (g : SU3) (x : fund) (φ : antifund) (v : irrepRep 1 1) :
    xiForm (fund.ρ g x) (antifund.ρ g φ) ((irrepRep 1 1).ρ g v) = xiForm x φ v := by
  change (show Module.Dual ℂ fund from (fundᘁ).ρ g φ)
    ((psi ((irrepRep 1 1).ρ g v)).mulVec (fund.ρ g x)) = _
  refine (dual_ρ_apply fund g φ _).trans ?_
  rw [psi_equivariant]
  change (show Module.Dual ℂ (Fin 3 → ℂ) from φ) ((star g.1).mulVec
    ((g.1 * psi v * star g.1).mulVec (g.1.mulVec (show Fin 3 → ℂ from x)))) = _
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have : star g.1 * (g.1 * psi v * star g.1) * g.1 = psi v := by
    simp only [← Matrix.mul_assoc, unitary_left, Matrix.one_mul]
    rw [Matrix.mul_assoc, unitary_left, Matrix.mul_one]
  rw [this]
  rfl

/-- **`ξᵀXη` is nonzero:** `e₁*(E₁₀ e₀) = 1`. -/
theorem xiForm_witness : ∃ v : irrepRep 1 1,
    xiForm (show fund from (Pi.single 0 1 : Fin 3 → ℂ))
      (show antifund from (LinearMap.proj 1 : (Fin 3 → ℂ) →ₗ[ℂ] ℂ)) v = 1 := by
  obtain ⟨v, hv⟩ := exists_psi (E 1 0) (by simp [Matrix.trace])
  refine ⟨v, ?_⟩
  rw [xiForm_apply, hv]
  simp

/-! ## (c) The `f`-type form `tr(X[Y, Z])` and the `d`-type form `tr(X{Y, Z})` on `8 ⊗ 8 ⊗ 8` -/

/-- `tr(X(YZ ± ZY))` on `8 × 8 × 8`; `s = -1` is the `f`-type, `s = 1` the `d`-type form. -/
noncomputable def adjForm (s : ℂ) :
    irrepRep 1 1 →ₗ[ℂ] irrepRep 1 1 →ₗ[ℂ] irrepRep 1 1 →ₗ[ℂ] ℂ :=
  mk3 (fun x y z => (psi x * (psi y * psi z + s • (psi z * psi y))).trace)
    (fun x x' y z => by simp [Matrix.add_mul, Matrix.trace_add])
    (fun c x y z => by simp [Matrix.trace_smul])
    (fun x y y' z => by
      simp only [map_add, Matrix.add_mul, Matrix.mul_add, smul_add, Matrix.trace_add]; ring)
    (fun c x y z => by
      simp only [map_smul, Matrix.smul_mul, Matrix.mul_smul, smul_comm s c, ← smul_add,
        Matrix.trace_smul, smul_eq_mul])
    (fun x y z z' => by
      simp only [map_add, Matrix.add_mul, Matrix.mul_add, smul_add, Matrix.trace_add]; ring)
    (fun c x y z => by
      simp only [map_smul, Matrix.smul_mul, Matrix.mul_smul, smul_comm s c, ← smul_add,
        Matrix.trace_smul, smul_eq_mul])

/-- The `f`-type invariant `tr(X[Y, Z])`. -/
noncomputable def fForm := adjForm (-1)

/-- The `d`-type invariant `tr(X{Y, Z})`. -/
noncomputable def dForm := adjForm 1

theorem adjForm_apply (s : ℂ) (x y z : irrepRep 1 1) :
    adjForm s x y z = (psi x * (psi y * psi z + s • (psi z * psi y))).trace := rfl

theorem adjForm_invariant (s : ℂ) (g : SU3) (x y z : irrepRep 1 1) :
    adjForm s ((irrepRep 1 1).ρ g x) ((irrepRep 1 1).ρ g y) ((irrepRep 1 1).ρ g z) =
      adjForm s x y z := by
  rw [adjForm_apply, adjForm_apply, psi_equivariant, psi_equivariant, psi_equivariant,
    ad_mul, ad_mul]
  have hs : s • (g.1 * (psi z * psi y) * star g.1) = g.1 * (s • (psi z * psi y)) * star g.1 := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [hs, ad_add, ad_mul, trace_ad]

/-- **`tr(X[Y, Z])` is SU(3)-invariant.** -/
theorem fForm_invariant (g : SU3) (x y z : irrepRep 1 1) :
    fForm ((irrepRep 1 1).ρ g x) ((irrepRep 1 1).ρ g y) ((irrepRep 1 1).ρ g z) =
      fForm x y z := adjForm_invariant _ g x y z

/-- **`tr(X{Y, Z})` is SU(3)-invariant.** -/
theorem dForm_invariant (g : SU3) (x y z : irrepRep 1 1) :
    dForm ((irrepRep 1 1).ρ g x) ((irrepRep 1 1).ρ g y) ((irrepRep 1 1).ρ g z) =
      dForm x y z := adjForm_invariant _ g x y z

/-- **`tr(X[Y, Z])` is nonzero:** `X = E₀₀ - E₁₁`, `Y = E₀₁`, `Z = E₁₀` give `2`. -/
theorem fForm_witness : ∃ x y z : irrepRep 1 1, fForm x y z = 2 := by
  obtain ⟨x, hx⟩ := exists_psi (E 0 0 - E 1 1) (by simp [Matrix.trace, Fin.sum_univ_three])
  obtain ⟨y, hy⟩ := exists_psi (E 0 1) (by simp [Matrix.trace])
  obtain ⟨z, hz⟩ := exists_psi (E 1 0) (by simp [Matrix.trace])
  refine ⟨x, y, z, ?_⟩
  rw [fForm, adjForm_apply, hx, hy, hz]
  simp [Matrix.trace, Fin.sum_univ_three, Matrix.mul_apply, Matrix.sub_apply]
  norm_num

/-- **`tr(X{Y, Z})` is nonzero:** `X = Y = Z = diag(1, 1, -2)` gives `2 tr X³ = -12`. -/
theorem dForm_witness : ∃ x : irrepRep 1 1, dForm x x x = -12 := by
  obtain ⟨x, hx⟩ := exists_psi (E 0 0 + E 1 1 - 2 • E 2 2)
    (by simp [Matrix.trace, Fin.sum_univ_three]; norm_num)
  refine ⟨x, ?_⟩
  rw [dForm, adjForm_apply, hx]
  simp [Matrix.trace, Fin.sum_univ_three, Matrix.mul_apply]
  norm_num

/-! ## Incoming theta vertices from the forms -/

/-- The trace form is nonzero. -/
theorem trForm_ne : ∃ x y : irrepRep 1 1, trForm x y (1 : ℂ) ≠ 0 := by
  obtain ⟨x, y, h⟩ := trForm_witness
  exact ⟨x, y, by rw [h]; exact one_ne_zero⟩

/-- Incoming vertex `(1, 8, 8)` on `V(0,0)`, `V(1,1)`, `V(1,1)`, by `tr(XY)`. -/
theorem in_1_8_8 :
    Representation.invariants (thetaVertex false (irrepRep 0 0) (irrepRep 1 1) (irrepRep 1 1)).ρ ≠ ⊥ := by
  obtain ⟨x, y, h⟩ := trForm_ne
  exact invariants_ne_bot_of_iso (thetaVertexIso false irrep00Iso (Iso.refl _) (Iso.refl _))
    (incoming_of_trilinear trForm trForm_invariant x y (1 : ℂ) h)

/-- Incoming vertex `(8, 3̄, 3)` on `V(1,1)`, `V(0,1)`, `V(1,0)`, by `ξᵀXη`. -/
theorem in_8_3b_3 :
    Representation.invariants (thetaVertex false (irrepRep 1 1) (irrepRep 0 1) (irrepRep 1 0)).ρ ≠ ⊥ := by
  obtain ⟨v, h⟩ := xiForm_witness
  exact invariants_ne_bot_of_iso (thetaVertexIso false (Iso.refl _) irrep01Iso irrep10Iso)
    (incoming_of_trilinear xiForm xiForm_invariant _ _ v (by rw [h]; exact one_ne_zero))

/-- Incoming vertex `(8, 8, 8)`, by `tr(X[Y, Z])`. -/
theorem in_8_8_8 :
    Representation.invariants (thetaVertex false (irrepRep 1 1) (irrepRep 1 1) (irrepRep 1 1)).ρ ≠ ⊥ := by
  obtain ⟨x, y, z, h⟩ := fForm_witness
  exact incoming_of_trilinear fForm fForm_invariant x y z (by rw [h]; norm_num)

/-- Incoming vertex `(8, 8, 8)`, independently by the `d`-type form `tr(X{Y, Z})`. -/
theorem in_8_8_8_d :
    Representation.invariants (thetaVertex false (irrepRep 1 1) (irrepRep 1 1) (irrepRep 1 1)).ρ ≠ ⊥ := by
  obtain ⟨x, h⟩ := dForm_witness
  exact incoming_of_trilinear dForm dForm_invariant x x x (by rw [h]; norm_num)

theorem in_8_1_8 :
    Representation.invariants (thetaVertex false (irrepRep 1 1) (irrepRep 0 0) (irrepRep 1 1)).ρ ≠ ⊥ :=
  perm12 in_1_8_8
theorem in_8_8_1 :
    Representation.invariants (thetaVertex false (irrepRep 1 1) (irrepRep 1 1) (irrepRep 0 0)).ρ ≠ ⊥ :=
  perm23 in_8_1_8
theorem in_8_3_3b :
    Representation.invariants (thetaVertex false (irrepRep 1 1) (irrepRep 1 0) (irrepRep 0 1)).ρ ≠ ⊥ :=
  perm23 in_8_3b_3
theorem in_3b_8_3 :
    Representation.invariants (thetaVertex false (irrepRep 0 1) (irrepRep 1 1) (irrepRep 1 0)).ρ ≠ ⊥ :=
  perm12 in_8_3b_3
theorem in_3b_3_8 :
    Representation.invariants (thetaVertex false (irrepRep 0 1) (irrepRep 1 0) (irrepRep 1 1)).ρ ≠ ⊥ :=
  perm23 in_3b_8_3
theorem in_3_8_3b :
    Representation.invariants (thetaVertex false (irrepRep 1 0) (irrepRep 1 1) (irrepRep 0 1)).ρ ≠ ⊥ :=
  perm12 in_8_3_3b
theorem in_3_3b_8 :
    Representation.invariants (thetaVertex false (irrepRep 1 0) (irrepRep 0 1) (irrepRep 1 1)).ρ ≠ ⊥ :=
  perm23 in_3_8_3b

/-! ## Conjugation isomorphisms and the outgoing vertices -/

/-- `V(1, 0) ≅ V(0, 1)ᘁ` (`3 ≅ 3ᘁᘁ = 3̄ᘁ`). -/
noncomputable def conj10 : irrepRep 1 0 ≅ (irrepRep 0 1)ᘁ :=
  irrep10Iso ≪≫ ddIso fund ≪≫ (dualIso irrep01Iso).symm

/-- `V(0, 1) ≅ V(1, 0)ᘁ` (`3̄ = 3ᘁ`). -/
noncomputable def conj01 : irrepRep 0 1 ≅ (irrepRep 1 0)ᘁ :=
  irrep01Iso ≪≫ (dualIso irrep10Iso).symm

/-- `V(0, 0) ≅ V(0, 0)ᘁ`. -/
noncomputable def conj00 : irrepRep 0 0 ≅ (irrepRep 0 0)ᘁ :=
  irrep00Iso ≪≫ (dualIsoUnitOfIso irrep00Iso.symm).symm

/-- `8ᘁ ⊗ 8ᘁ` has a nonzero invariant (the trace form). -/
theorem invariants_dual11_dual11_ne_bot :
    Representation.invariants ((irrepRep 1 1)ᘁ ⊗ (irrepRep 1 1)ᘁ).ρ ≠ ⊥ := by
  obtain ⟨x, y, h⟩ := trForm_ne
  have h1 := dual_invariants_ne_bot_of_form
    (X := irrepRep 1 1 ⊗ (irrepRep 1 1 ⊗ 𝟙_ (FDRep ℂ SU3))) (form3 trForm) (form3_invariant trForm trForm_invariant)
    (form3_ne_zero trForm x y (1 : ℂ) h)
  exact invariants_ne_bot_of_iso ((dualTensorIso _ _).symm ≪≫
    dualIso (whiskerLeftIso (irrepRep 1 1) (ρ_ (irrepRep 1 1)).symm)) h1

/-- **The adjoint is self-dual: `V(1, 1) ≅ V(1, 1)ᘁ`.** From the invariant trace form, the
simplicity of `V(1, 1)` (`simple_irrep11`) and Schur (`iso_of_pair_invariant`). -/
theorem irrep11_self_dual : Nonempty (irrepRep 1 1 ≅ (irrepRep 1 1)ᘁ) := by
  have := simple_irrep11
  have : Simple (irrepRep 1 1)ᘁ := dual_simple _
  have : Simple ((irrepRep 1 1)ᘁ : FDRep ℂ SU3)ᘁ := dual_simple _
  obtain ⟨j⟩ := iso_of_pair_invariant ((irrepRep 1 1)ᘁ) (((irrepRep 1 1)ᘁ : FDRep ℂ SU3)ᘁ)
    ((irrepRep 1 1)ᘁ) invariants_dual11_dual11_ne_bot
  exact ⟨ddIso _ ≪≫ j⟩

/-! ## The adjoint rows of the theta table -/

/-- Row `(3̄, 3, 8)`: attained at both theta vertices (`ξᵀXη`). -/
theorem row_3bar_3_8 : ((0, 1), (1, 0), (1, 1)) ∈ thetaList ∧
    Representation.invariants (thetaVertex true (irrepRep 0 1) (irrepRep 1 0) (irrepRep 1 1)).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false (irrepRep 0 1) (irrepRep 1 0) (irrepRep 1 1)).ρ ≠ ⊥ := by
  obtain ⟨c8⟩ := irrep11_self_dual
  exact ⟨by decide, outgoing_of_incoming conj01 conj10 c8 in_3_3b_8, in_3b_3_8⟩

/-- Row `(3̄, 8, 3)`. -/
theorem row_3bar_8_3 : ((0, 1), (1, 1), (1, 0)) ∈ thetaList ∧
    Representation.invariants (thetaVertex true (irrepRep 0 1) (irrepRep 1 1) (irrepRep 1 0)).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false (irrepRep 0 1) (irrepRep 1 1) (irrepRep 1 0)).ρ ≠ ⊥ := by
  obtain ⟨c8⟩ := irrep11_self_dual
  exact ⟨by decide, outgoing_of_incoming conj01 c8 conj10 in_3_8_3b, in_3b_8_3⟩

/-- Row `(3, 3̄, 8)`. -/
theorem row_3_3bar_8 : ((1, 0), (0, 1), (1, 1)) ∈ thetaList ∧
    Representation.invariants (thetaVertex true (irrepRep 1 0) (irrepRep 0 1) (irrepRep 1 1)).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false (irrepRep 1 0) (irrepRep 0 1) (irrepRep 1 1)).ρ ≠ ⊥ := by
  obtain ⟨c8⟩ := irrep11_self_dual
  exact ⟨by decide, outgoing_of_incoming conj10 conj01 c8 in_3b_3_8, in_3_3b_8⟩

/-- Row `(3, 8, 3̄)`. -/
theorem row_3_8_3bar : ((1, 0), (1, 1), (0, 1)) ∈ thetaList ∧
    Representation.invariants (thetaVertex true (irrepRep 1 0) (irrepRep 1 1) (irrepRep 0 1)).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false (irrepRep 1 0) (irrepRep 1 1) (irrepRep 0 1)).ρ ≠ ⊥ := by
  obtain ⟨c8⟩ := irrep11_self_dual
  exact ⟨by decide, outgoing_of_incoming conj10 c8 conj01 in_3b_8_3, in_3_8_3b⟩

/-- Row `(8, 3̄, 3)`. -/
theorem row_8_3bar_3 : ((1, 1), (0, 1), (1, 0)) ∈ thetaList ∧
    Representation.invariants (thetaVertex true (irrepRep 1 1) (irrepRep 0 1) (irrepRep 1 0)).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false (irrepRep 1 1) (irrepRep 0 1) (irrepRep 1 0)).ρ ≠ ⊥ := by
  obtain ⟨c8⟩ := irrep11_self_dual
  exact ⟨by decide, outgoing_of_incoming c8 conj01 conj10 in_8_3_3b, in_8_3b_3⟩

/-- Row `(8, 3, 3̄)`. -/
theorem row_8_3_3bar : ((1, 1), (1, 0), (0, 1)) ∈ thetaList ∧
    Representation.invariants (thetaVertex true (irrepRep 1 1) (irrepRep 1 0) (irrepRep 0 1)).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false (irrepRep 1 1) (irrepRep 1 0) (irrepRep 0 1)).ρ ≠ ⊥ := by
  obtain ⟨c8⟩ := irrep11_self_dual
  exact ⟨by decide, outgoing_of_incoming c8 conj10 conj01 in_8_3b_3, in_8_3_3b⟩

/-- Row `(8, 1, 8)`: attained at both theta vertices (`tr(XY)`). -/
theorem row_8_1_8 : ((1, 1), (0, 0), (1, 1)) ∈ thetaList ∧
    Representation.invariants (thetaVertex true (irrepRep 1 1) (irrepRep 0 0) (irrepRep 1 1)).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false (irrepRep 1 1) (irrepRep 0 0) (irrepRep 1 1)).ρ ≠ ⊥ := by
  obtain ⟨c8⟩ := irrep11_self_dual
  exact ⟨by decide, outgoing_of_incoming c8 conj00 c8 in_8_1_8, in_8_1_8⟩

/-- Row `(8, 8, 1)`. -/
theorem row_8_8_1 : ((1, 1), (1, 1), (0, 0)) ∈ thetaList ∧
    Representation.invariants (thetaVertex true (irrepRep 1 1) (irrepRep 1 1) (irrepRep 0 0)).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false (irrepRep 1 1) (irrepRep 1 1) (irrepRep 0 0)).ρ ≠ ⊥ := by
  obtain ⟨c8⟩ := irrep11_self_dual
  exact ⟨by decide, outgoing_of_incoming c8 c8 conj00 in_8_8_1, in_8_8_1⟩

/-- **The `(8, 8, 8)` vertex** (`tr(X[Y, Z])`): both theta vertices with three adjoint arms
have a nonzero invariant. Not a row of `thetaList`: its level is `63/3 > 17`. -/
theorem row_8_8_8 : ((1, 1), (1, 1), (1, 1)) ∉ thetaList ∧ level3 (1, 1) (1, 1) (1, 1) = 63 ∧
    Representation.invariants (thetaVertex true (irrepRep 1 1) (irrepRep 1 1) (irrepRep 1 1)).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false (irrepRep 1 1) (irrepRep 1 1) (irrepRep 1 1)).ρ ≠ ⊥ := by
  obtain ⟨c8⟩ := irrep11_self_dual
  exact ⟨by decide, by decide, outgoing_of_incoming c8 c8 c8 in_8_8_8, in_8_8_8⟩

/-- The eight rows of the theta table with an octet arm and all other arms in `{1, 3, 3̄}`. -/
def adjointRows : List (Irrep × Irrep × Irrep) :=
  [((0, 1), (1, 0), (1, 1)), ((0, 1), (1, 1), (1, 0)), ((1, 0), (0, 1), (1, 1)),
   ((1, 0), (1, 1), (0, 1)), ((1, 1), (0, 0), (1, 1)), ((1, 1), (0, 1), (1, 0)),
   ((1, 1), (1, 0), (0, 1)), ((1, 1), (1, 1), (0, 0))]

/-- The labels `{1, 3, 3̄, 8}`. -/
def smallAdj : List Irrep := [(0, 0), (1, 0), (0, 1), (1, 1)]

/-- **`adjointRows` are exactly the rows of `thetaList` with an octet arm whose arms all lie in
`{1, 3, 3̄, 8}`.** -/
theorem adjointRows_iff (t : Irrep × Irrep × Irrep) :
    t ∈ adjointRows ↔ t ∈ thetaList ∧ (t.1 = (1, 1) ∨ t.2.1 = (1, 1) ∨ t.2.2 = (1, 1)) ∧
      t.1 ∈ smallAdj ∧ t.2.1 ∈ smallAdj ∧ t.2.2 ∈ smallAdj := by
  have h1 : ∀ t ∈ adjointRows, t ∈ thetaList ∧ (t.1 = (1, 1) ∨ t.2.1 = (1, 1) ∨ t.2.2 = (1, 1)) ∧
      t.1 ∈ smallAdj ∧ t.2.1 ∈ smallAdj ∧ t.2.2 ∈ smallAdj := by decide
  have h2 : ∀ t ∈ thetaList, ((t.1 = (1, 1) ∨ t.2.1 = (1, 1) ∨ t.2.2 = (1, 1)) ∧
      t.1 ∈ smallAdj ∧ t.2.1 ∈ smallAdj ∧ t.2.2 ∈ smallAdj) → t ∈ adjointRows := by decide
  exact ⟨fun h => h1 t h, fun ⟨h, h'⟩ => h2 t h h'⟩

theorem adjointRows_length : adjointRows.length = 8 := rfl

/-- **The eight adjoint rows are attained on the arms `V(a)`, `V(b)`, `V(c)` themselves:** each
is in the theta table and both theta vertices have a nonzero invariant. -/
theorem adjointRows_irrep_both (t : Irrep × Irrep × Irrep) (ht : t ∈ adjointRows) :
    t ∈ thetaList ∧
    Representation.invariants (thetaVertex true (irrepRep t.1.1 t.1.2)
      (irrepRep t.2.1.1 t.2.1.2) (irrepRep t.2.2.1 t.2.2.2)).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false (irrepRep t.1.1 t.1.2)
      (irrepRep t.2.1.1 t.2.1.2) (irrepRep t.2.2.1 t.2.2.2)).ρ ≠ ⊥ := by
  simp only [adjointRows, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row_3bar_3_8
  · exact row_3bar_8_3
  · exact row_3_3bar_8
  · exact row_3_8_3bar
  · exact row_8_1_8
  · exact row_8_3bar_3
  · exact row_8_3_3bar
  · exact row_8_8_1

/-- All attained rows: the eight of `attainedRows` (arms in `{1, 3, 3̄}`) and the eight adjoint
rows. -/
def allAttainedRows : List (Irrep × Irrep × Irrep) := attainedRows ++ adjointRows

/-- **16 rows are attained.** -/
theorem allAttainedRows_length : allAttainedRows.length = 16 := rfl

/-- The attained rows are exactly the rows of `thetaList` whose arms all lie in
`{1, 3, 3̄, 8}`. -/
theorem allAttainedRows_iff (t : Irrep × Irrep × Irrep) :
    t ∈ allAttainedRows ↔ t ∈ thetaList ∧
      t.1 ∈ smallAdj ∧ t.2.1 ∈ smallAdj ∧ t.2.2 ∈ smallAdj := by
  have h1 : ∀ t ∈ allAttainedRows, t ∈ thetaList ∧
      t.1 ∈ smallAdj ∧ t.2.1 ∈ smallAdj ∧ t.2.2 ∈ smallAdj := by decide
  have h2 : ∀ t ∈ thetaList, (t.1 ∈ smallAdj ∧ t.2.1 ∈ smallAdj ∧ t.2.2 ∈ smallAdj) →
      t ∈ allAttainedRows := by decide
  exact ⟨fun h => h1 t h, fun ⟨h, h'⟩ => h2 t h h'⟩

/-- **All 16 attained rows, on the `V(p, q)` arms:** in the theta table, with a nonzero
invariant at both theta vertices. -/
theorem allAttainedRows_irrep_both (t : Irrep × Irrep × Irrep) (ht : t ∈ allAttainedRows) :
    t ∈ thetaList ∧
    Representation.invariants (thetaVertex true (irrepRep t.1.1 t.1.2)
      (irrepRep t.2.1.1 t.2.1.2) (irrepRep t.2.2.1 t.2.2.2)).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false (irrepRep t.1.1 t.1.2)
      (irrepRep t.2.1.1 t.2.1.2) (irrepRep t.2.2.1 t.2.2.2)).ρ ≠ ⊥ := by
  rcases List.mem_append.1 ht with h | h
  · exact attainedRows_irrep_both t h
  · exact adjointRows_irrep_both t h

/-- The eight rows with an octet arm not covered here: each also has a sextet arm. -/
def adjointOpenRows : List (Irrep × Irrep × Irrep) :=
  [((0, 2), (0, 1), (1, 1)), ((0, 2), (1, 1), (0, 1)), ((1, 1), (0, 1), (0, 2)),
   ((1, 1), (0, 2), (0, 1)), ((1, 1), (1, 0), (2, 0)), ((1, 1), (2, 0), (1, 0)),
   ((2, 0), (1, 0), (1, 1)), ((2, 0), (1, 1), (1, 0))]

/-- `adjointOpenRows` are exactly the rows of `thetaList` with an octet arm and an arm outside
`{1, 3, 3̄, 8}`. -/
theorem adjointOpenRows_iff (t : Irrep × Irrep × Irrep) :
    t ∈ adjointOpenRows ↔ t ∈ thetaList ∧ (t.1 = (1, 1) ∨ t.2.1 = (1, 1) ∨ t.2.2 = (1, 1)) ∧
      ¬ (t.1 ∈ smallAdj ∧ t.2.1 ∈ smallAdj ∧ t.2.2 ∈ smallAdj) := by
  have h1 : ∀ t ∈ adjointOpenRows, t ∈ thetaList ∧
      (t.1 = (1, 1) ∨ t.2.1 = (1, 1) ∨ t.2.2 = (1, 1)) ∧
      ¬ (t.1 ∈ smallAdj ∧ t.2.1 ∈ smallAdj ∧ t.2.2 ∈ smallAdj) := by decide
  have h2 : ∀ t ∈ thetaList, ((t.1 = (1, 1) ∨ t.2.1 = (1, 1) ∨ t.2.2 = (1, 1)) ∧
      ¬ (t.1 ∈ smallAdj ∧ t.2.1 ∈ smallAdj ∧ t.2.2 ∈ smallAdj)) → t ∈ adjointOpenRows := by
    decide
  exact ⟨fun h => h1 t h, fun ⟨h, h'⟩ => h2 t h h'⟩

/-- Of the 34 rows, 18 are not attained here. -/
theorem not_attained_count :
    (thetaList.filter fun t => decide (t ∉ allAttainedRows)).length = 18 := by decide

/-! ## The control: `3 ⊗ 8` has no nonzero invariant -/

/-- `ω·I` acts on `3 ⊗ 8` by `ω · 1 = ω`. -/
theorem centreActs_fund_adjoint : CentreActs zω ω (fund ⊗ irrepRep 1 1) := by
  have h := centreActs_tensor centreActs_fund (adjoint_centre_trivial (irrepIncl 1 1))
  rwa [mul_one] at h

/-- **`3 ⊗ 8` has no nonzero invariant** (triality `1 + 0 ≢ 0`): the negation of the false
control. -/
theorem invariants_fund_adjoint_eq_bot :
    Representation.invariants (fund ⊗ irrepRep 1 1).ρ = ⊥ := by
  by_contra h
  exact omega_ne_one (scalar_eq_one_of_invariant centreActs_fund_adjoint h)

/-- The same on the arms `V(1, 0) ⊗ V(1, 1)`. -/
theorem invariants_irrep10_irrep11_eq_bot :
    Representation.invariants (irrepRep 1 0 ⊗ irrepRep 1 1).ρ = ⊥ :=
  (invariants_eq_bot_iff_of_iso (irrep10Iso ⊗ᵢ Iso.refl _)).2 invariants_fund_adjoint_eq_bot

end AdjointWitnessSU3
