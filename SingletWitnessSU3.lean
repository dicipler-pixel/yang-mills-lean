import ThetaFloorTriality

/-!
# Explicit SU(3) singlets: the smallest theta rows are attained

Author: Jeromie Beasley (Spectrum · Colour team lead, Grok Bot), with the Team.
ORCID https://orcid.org/0009-0006-4645-5643 · GitHub dicipler-pixel · X @d1c1pler ·
YouTube @AtlasMemoriae · atlas-memoriae.dicipler.workers.dev

`ThetaFloorTriality` proves the necessary direction of the singlet rule: a nonzero invariant at
a vertex forces its triality to vanish. This file proves the converse for the smallest rows by
explicit witness, in the representations `fund = 3` (matrix action on `ℂ³`) and
`antifund = 3̄ = 3ᘁ` (dual action `φ ↦ φ ∘ g⁻¹`) of `CentreCharacterSU3`.

**Witnesses (each nonzero and SU(3)-invariant).**
* `traceVec = ∑ᵢ eᵢ ⊗ eᵢ* ∈ 3 ⊗ 3̄` (`traceVec_invariant`, `traceVec_ne_zero`), from
  `g g⁻¹ = 1`: `g` moves `eᵢ` by `g` and `eᵢ*` by `(g⁻¹)ᵀ`.
* `epsVec3 = ∑ ε_{ijk} eᵢ ⊗ eⱼ ⊗ e_k ∈ 3 ⊗ 3 ⊗ 3` (`epsVec3_invariant`, `epsVec3_ne_zero`), from
  `∑ ε_{ijk} g_{ai} g_{bj} g_{ck} = det g · ε_{abc}` (`eps_contract`) and `det g = 1`.
* `epsVec3bar = ∑ ε_{ijk} eᵢ* ⊗ eⱼ* ⊗ e_k* ∈ 3̄ ⊗ 3̄ ⊗ 3̄` (`epsVec3bar_invariant`,
  `epsVec3bar_ne_zero`), from `det (g⁻¹)ᵀ = 1`. For unitary `g`, `(g⁻¹)ᵀ = conj g`, so this is
  `det (conj g) = conj (det g) = 1`.

The computations are done once on plain modules (`pair_raw`, `eps_raw`) for any three vectors
that `g` moves by a matrix (`Frame`), and transported to tensor products with trivial factors
and to duals (`frameTensorSinglet`, `singletTensorFrame`, `frameDDual`, `singletUnitDual`).

**Theta rows attained.** For each of the eight rows of `thetaList` whose arms lie in
`{(0,0), (1,0), (0,1)}` (`attainedRows_iff`), with `(1,0)` carried by `3`, `(0,1)` by `3̄` and
`(0,0)` by `𝟙`, both theta vertices (all arms outgoing, `A ⊗ B ⊗ C`; all incoming,
`Aᘁ ⊗ Bᘁ ⊗ Cᘁ`) have a nonzero invariant (`vertexRep` of `GaugeSupportLattice`):
* `row_1_3bar_3`, `row_1_3_3bar`, `row_3bar_1_3`, `row_3bar_3_1`, `row_3_1_3bar`,
  `row_3_3bar_1`: the six orderings of `(1, 3̄, 3)`, by the trace witness;
* `row_3_3_3`: `(3, 3, 3)`, by `ε` at the first vertex and `ε*` at the second;
* `row_3bar_3bar_3bar`: `(3̄, 3̄, 3̄)`, by `ε*` and by `ε` on `3̄ᘁ`.
So these rows are attained, not only allowed.

**Control.** `epsMixed`, the same components `ε_{ijk}` placed in `3 ⊗ 3 ⊗ 3̄`, is not
invariant: `ω·I` scales it by `ω · ω · ω² = ω ≠ 1` (`epsMixed_centre`,
`epsMixed_not_invariant`); indeed `3 ⊗ 3 ⊗ 3̄` has no nonzero invariant at all
(`invariants_mixed_eq_bot`). `FalseControls/EpsilonMixedControl.lean` claims the invariance.

**Not proved (open).**
* The general sufficiency direction: that the BMW inequalities plus vanishing triality give a
  nonzero invariant of `V(a) ⊗ V(b) ⊗ V(c)` for every admissible row.
* The rows here use `3`, `3̄`, `𝟙` themselves as arms. That these are isomorphic to
  `V(1,0)`, `V(0,1)`, `V(0,0)` of `IrrepEmbedSU3` (i.e. that each of those cyclic subspaces is
  the whole of `3 ⊗ 𝟙`, `3̄ ⊗ 𝟙`, `𝟙`) is not formalized here.

No continuum or mass-gap statement is made.
-/

open CategoryTheory MonoidalCategory ThetaFloor ThetaTriality TrialityVertex GaugeSupport
  CentreCharacterSU3 IrrepEmbedSU3

namespace SingletWitnessSU3

/-- Three vectors of `X` that `g` moves by the matrix `M g`, with dual coordinate functionals. -/
structure Frame (X : FDRep ℂ SU3) (M : SU3 → Matrix (Fin 3) (Fin 3) ℂ) where
  u : Fin 3 → X
  ℓ : Fin 3 → (X →ₗ[ℂ] ℂ)
  moves : ∀ g i, X.ρ g (u i) = ∑ a, M g a i • u a
  coord : ∀ i j, ℓ i (u j) = if i = j then 1 else 0

/-- A nonzero invariant vector, with a functional that detects it. -/
structure Singlet (X : FDRep ℂ SU3) where
  v : X
  ℓ : X →ₗ[ℂ] ℂ
  inv : ∀ g, X.ρ g v = v
  coord : ℓ v = 1

theorem Singlet.ne_zero {X : FDRep ℂ SU3} (s : Singlet X) : s.v ≠ 0 := by
  intro h
  have := s.coord
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem Singlet.invariants_ne_bot {X : FDRep ℂ SU3} (s : Singlet X) :
    Representation.invariants X.ρ ≠ ⊥ := by
  intro h
  have hv : s.v ∈ Representation.invariants X.ρ := fun g => s.inv g
  rw [h, Submodule.mem_bot] at hv
  exact s.ne_zero hv

/-- The functional on `X ⊗ Y` built from functionals on the factors. -/
noncomputable def pairFun {X Y : FDRep ℂ SU3} (f : X →ₗ[ℂ] ℂ) (f' : Y →ₗ[ℂ] ℂ) :
    (X ⊗ Y : FDRep ℂ SU3) →ₗ[ℂ] ℂ :=
  ((TensorProduct.lid ℂ ℂ).toLinearMap ∘ₗ TensorProduct.map f f' :
    TensorProduct ℂ X Y →ₗ[ℂ] ℂ)

theorem pairFun_tmul {X Y : FDRep ℂ SU3} (f : X →ₗ[ℂ] ℂ) (f' : Y →ₗ[ℂ] ℂ) (x : X) (y : Y) :
    pairFun f f' (x ⊗ₜ[ℂ] y : TensorProduct ℂ X Y) = f x * f' y := by
  change (TensorProduct.lid ℂ ℂ) (TensorProduct.map f f' (x ⊗ₜ[ℂ] y)) = _
  rw [TensorProduct.map_tmul, TensorProduct.lid_tmul, smul_eq_mul]

theorem tensor_ρ_tmul {X Y : FDRep ℂ SU3} (g : SU3) (x : X) (y : Y) :
    (X ⊗ Y).ρ g (x ⊗ₜ[ℂ] y : TensorProduct ℂ X Y) =
      (X.ρ g x ⊗ₜ[ℂ] Y.ρ g y : TensorProduct ℂ X Y) := by
  change TensorProduct.map (X.ρ g) (Y.ρ g) (x ⊗ₜ[ℂ] y) = _
  rw [TensorProduct.map_tmul]

/-- The unit object `𝟙 = ℂ` with the vector `1`. -/
noncomputable def singletUnit : Singlet (𝟙_ (FDRep ℂ SU3)) where
  v := (1 : ℂ)
  ℓ := (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
  inv _ := rfl
  coord := rfl

/-- Two singlets tensor to a singlet. -/
noncomputable def singletTensor {X Y : FDRep ℂ SU3} (s : Singlet X) (t : Singlet Y) :
    Singlet (X ⊗ Y) where
  v := (s.v ⊗ₜ[ℂ] t.v : TensorProduct ℂ X Y)
  ℓ := pairFun s.ℓ t.ℓ
  inv g := by rw [tensor_ρ_tmul, s.inv, t.inv]
  coord := by rw [pairFun_tmul, s.coord, t.coord, one_mul]

/-- A frame tensored on the right with a singlet. -/
noncomputable def frameTensorSinglet {X Y : FDRep ℂ SU3} {M : SU3 → Matrix (Fin 3) (Fin 3) ℂ}
    (F : Frame X M) (t : Singlet Y) : Frame (X ⊗ Y) M where
  u i := (F.u i ⊗ₜ[ℂ] t.v : TensorProduct ℂ X Y)
  ℓ i := pairFun (F.ℓ i) t.ℓ
  moves g i := by
    rw [tensor_ρ_tmul, F.moves, t.inv]
    change (∑ a, M g a i • F.u a) ⊗ₜ[ℂ] t.v = ∑ a, M g a i • ((F.u a ⊗ₜ[ℂ] t.v : TensorProduct ℂ X Y))
    rw [TensorProduct.sum_tmul]
    simp only [TensorProduct.smul_tmul']
  coord i j := by rw [pairFun_tmul, F.coord, t.coord, mul_one]

/-- A singlet tensored on the left of a frame. -/
noncomputable def singletTensorFrame {X Y : FDRep ℂ SU3} {M : SU3 → Matrix (Fin 3) (Fin 3) ℂ}
    (s : Singlet X) (F : Frame Y M) : Frame (X ⊗ Y) M where
  u i := (s.v ⊗ₜ[ℂ] F.u i : TensorProduct ℂ X Y)
  ℓ i := pairFun s.ℓ (F.ℓ i)
  moves g i := by
    rw [tensor_ρ_tmul, F.moves, s.inv]
    change s.v ⊗ₜ[ℂ] (∑ a, M g a i • F.u a) = ∑ a, M g a i • ((s.v ⊗ₜ[ℂ] F.u a : TensorProduct ℂ X Y))
    rw [TensorProduct.tmul_sum]
    simp only [TensorProduct.tmul_smul]
  coord i j := by rw [pairFun_tmul, F.coord, s.coord, one_mul]

/-! ## Frames of `3`, `3̄` and `3̄ᘁ` -/

/-- The standard basis `e₀, e₁, e₂` of `3`; `g` moves it by the matrix `g`. -/
noncomputable def frameFund : Frame fund (fun g => g.1) where
  u i := (Pi.single i 1 : Fin 3 → ℂ)
  ℓ i := (LinearMap.proj i : (Fin 3 → ℂ) →ₗ[ℂ] ℂ)
  moves g i := by
    change Matrix.toLin' g.1 (Pi.single i 1) = ∑ a, g.1 a i • (Pi.single a 1 : Fin 3 → ℂ)
    funext b
    rw [Matrix.toLin'_apply, Matrix.mulVec_single_one, Finset.sum_apply]
    simp [Pi.single_apply]
  coord i j := by
    change (Pi.single j 1 : Fin 3 → ℂ) i = _
    simp [Pi.single_apply]

/-- The dual basis `e₀*, e₁*, e₂*` of `3̄`; `g` moves it by `(g⁻¹)ᵀ`. -/
noncomputable def frameAntifund : Frame antifund (fun g => (g⁻¹).1.transpose) where
  u i := (LinearMap.proj i : (Fin 3 → ℂ) →ₗ[ℂ] ℂ)
  ℓ i := Module.Dual.eval ℂ (Fin 3 → ℂ) (Pi.single i 1)
  moves g i := by
    change (show Module.Dual ℂ fund from fundᘁ.ρ g (LinearMap.proj i : (Fin 3 → ℂ) →ₗ[ℂ] ℂ)) =
      ∑ a, (g⁻¹).1.transpose a i • (LinearMap.proj a : (Fin 3 → ℂ) →ₗ[ℂ] ℂ)
    refine LinearMap.ext fun x => ?_
    refine (dual_ρ_apply fund g _ x).trans ?_
    have key : ∀ y : Fin 3 → ℂ, (LinearMap.proj i : (Fin 3 → ℂ) →ₗ[ℂ] ℂ)
        (Matrix.toLin' (g⁻¹).1 y) =
        (∑ a, (g⁻¹).1.transpose a i • (LinearMap.proj a : (Fin 3 → ℂ) →ₗ[ℂ] ℂ)) y := by
      intro y
      rw [LinearMap.sum_apply, Matrix.toLin'_apply]
      simp [Matrix.mulVec, dotProduct]
    exact key x
  coord i j := by
    change (Pi.single i 1 : Fin 3 → ℂ) j = _
    simp [Pi.single_apply, eq_comm]

/-- The double dual `Xᘁᘁ` with the evaluation vectors `ev(u i)`; they move like the `u i`. -/
noncomputable def frameDDual {X : FDRep ℂ SU3} {M : SU3 → Matrix (Fin 3) (Fin 3) ℂ}
    (F : Frame X M) : Frame (X : FDRep ℂ SU3)ᘁᘁ M where
  u i := (Module.Dual.eval ℂ X (F.u i) : Module.Dual ℂ (Module.Dual ℂ X))
  ℓ i := Module.Dual.eval ℂ (Module.Dual ℂ X) (F.ℓ i)
  moves g i := by
    refine LinearMap.ext fun φ => ?_
    refine (dual_ρ_apply ((X : FDRep ℂ SU3)ᘁ) g _ φ).trans ?_
    change (show Module.Dual ℂ X from ((X : FDRep ℂ SU3)ᘁ).ρ g⁻¹ φ) (F.u i) = _
    rw [dual_ρ_apply X g⁻¹ φ (F.u i), inv_inv, F.moves]
    change (show Module.Dual ℂ X from φ) (∑ a, M g a i • F.u a) =
      (∑ a, M g a i • Module.Dual.eval ℂ X (F.u a)) (show Module.Dual ℂ X from φ)
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul]
    rfl
  coord i j := F.coord i j

/-- A singlet whose detecting functional is itself invariant gives a singlet of the dual. -/
noncomputable def singletDual {X : FDRep ℂ SU3} (s : Singlet X)
    (hℓ : ∀ g x, s.ℓ (X.ρ g x) = s.ℓ x) : Singlet ((X : FDRep ℂ SU3)ᘁ) where
  v := (s.ℓ : Module.Dual ℂ X)
  ℓ := Module.Dual.eval ℂ X s.v
  inv g := by
    refine LinearMap.ext fun x => ?_
    exact (dual_ρ_apply X g _ x).trans (hℓ g⁻¹ x)
  coord := s.coord

/-- `𝟙ᘁ` has a singlet (the identity functional). -/
noncomputable def singletUnitDual :=
  singletDual singletUnit (fun _ _ => rfl)

/-! ## The two contractions -/

theorem sum3_comm {V : Type*} [AddCommMonoid V] (f : Fin 3 → Fin 3 → Fin 3 → V) :
    ∑ i, ∑ a, ∑ b, f i a b = ∑ a, ∑ b, ∑ i, f i a b := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem sum6_comm {V : Type*} [AddCommMonoid V]
    (f : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → V) :
    ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c, f i j k a b c =
      ∑ a, ∑ b, ∑ c, ∑ i, ∑ j, ∑ k, f i j k a b c := by
  have h1 : ∀ g : Fin 3 → Fin 3 → Fin 3 → V,
      ∑ a, ∑ b, ∑ c, g a b c = ∑ x : Fin 3 × Fin 3 × Fin 3, g x.1 x.2.1 x.2.2 := by
    intro g
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
  simp only [h1]
  exact Finset.sum_comm

theorem sum3_rot {V : Type*} [AddCommMonoid V] (f : Fin 3 → Fin 3 → Fin 3 → V) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ a, ∑ b, f a b c :=
  calc _ = ∑ a, ∑ c, ∑ b, f a b c := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- The Levi-Civita symbol `ε_{ijk}`. -/
def eps : Fin 3 → Fin 3 → Fin 3 → ℂ :=
  ![![![0, 0, 0], ![0, 0, 1], ![0, -1, 0]],
    ![![0, 0, -1], ![0, 0, 0], ![1, 0, 0]],
    ![![0, 1, 0], ![-1, 0, 0], ![0, 0, 0]]]

/-- `∑ ε_{ijk} M_{ai} M_{bj} M_{ck} = det M · ε_{abc}`. -/
theorem eps_contract (M : Matrix (Fin 3) (Fin 3) ℂ) (a b c : Fin 3) :
    ∑ i, ∑ j, ∑ k, eps i j k * (M a i * (M b j * M c k)) = M.det * eps a b c := by
  rw [Matrix.det_fin_three]
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [Fin.sum_univ_three, eps] <;> ring

/-- `∑ᵢ M_{ai} N_{bi} = (M Nᵀ)_{ab}`. -/
theorem pair_contract (M N : Matrix (Fin 3) (Fin 3) ℂ) (a b : Fin 3) :
    ∑ i, M a i * N b i = (M * N.transpose) a b := by
  simp [Matrix.mul_apply]

section Raw

variable {V W U : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]

/-- The pair contraction on plain modules. -/
theorem pair_raw (f : V →ₗ[ℂ] V) (f' : W →ₗ[ℂ] W) (u : Fin 3 → V) (w : Fin 3 → W)
    (m n : Fin 3 → Fin 3 → ℂ) (hu : ∀ i, f (u i) = ∑ a, m a i • u a)
    (hw : ∀ i, f' (w i) = ∑ a, n a i • w a)
    (h : ∀ a b, ∑ i, m a i * n b i = if a = b then 1 else 0) :
    TensorProduct.map f f' (∑ i, u i ⊗ₜ[ℂ] w i) = ∑ i, u i ⊗ₜ[ℂ] w i := by
  simp only [map_sum, TensorProduct.map_tmul, hu, hw, TensorProduct.sum_tmul,
    TensorProduct.tmul_sum, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul,
    Finset.smul_sum]
  rw [sum3_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [← Finset.sum_smul]
  simp [mul_comm (n _ _), h, ite_smul, Finset.sum_ite_eq']

/-- A pure tensor of two moved vectors moves by the product of the coefficients. -/
theorem tmul_raw (f : V →ₗ[ℂ] V) (f' : W →ₗ[ℂ] W) (u : Fin 3 → V) (w : Fin 3 → W)
    (m : Fin 3 → Fin 3 → ℂ) (hu : ∀ i, f (u i) = ∑ a, m a i • u a)
    (hw : ∀ i, f' (w i) = ∑ a, m a i • w a) (j k : Fin 3) :
    TensorProduct.map f f' (u j ⊗ₜ[ℂ] w k) = ∑ b, ∑ c, (m b j * m c k) • (u b ⊗ₜ[ℂ] w c) := by
  simp only [TensorProduct.map_tmul, hu, hw, TensorProduct.sum_tmul, TensorProduct.tmul_sum,
    ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  simp only [mul_comm]

/-- The ε contraction on plain modules: unchanged when `m` has determinant one. Here
`t j k` stands for `vⱼ ⊗ w_k` and moves by `m_{bj} m_{ck}`. -/
theorem eps_raw (f₁ : V →ₗ[ℂ] V) (f₂ : W →ₗ[ℂ] W) (u : Fin 3 → V) (t : Fin 3 → Fin 3 → W)
    (m : Fin 3 → Fin 3 → ℂ) (hu : ∀ i, f₁ (u i) = ∑ a, m a i • u a)
    (ht : ∀ j k, f₂ (t j k) = ∑ b, ∑ c, (m b j * m c k) • t b c)
    (h : ∀ a b c, ∑ i, ∑ j, ∑ k, eps i j k * (m a i * (m b j * m c k)) = eps a b c) :
    TensorProduct.map f₁ f₂ (∑ i, ∑ j, ∑ k, (eps i j k • u i) ⊗ₜ[ℂ] t j k) =
      ∑ i, ∑ j, ∑ k, (eps i j k • u i) ⊗ₜ[ℂ] t j k := by
  simp only [← TensorProduct.smul_tmul']
  simp only [map_sum, map_smul, TensorProduct.map_tmul, hu, ht, TensorProduct.sum_tmul,
    TensorProduct.tmul_sum, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul,
    Finset.smul_sum]
  rw [sum6_comm, sum3_rot]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => ?_
  simp only [← Finset.sum_smul]
  rw [← h c a b]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  ring

/-- The coordinate of the ε tensor at `(0, 1, 2)` is `1`. -/
theorem eps_coord_raw (u : Fin 3 → V) (t : Fin 3 → Fin 3 → W) (ℓ₁ : V →ₗ[ℂ] ℂ)
    (ℓ₂ : W →ₗ[ℂ] ℂ) (h₁ : ∀ j, ℓ₁ (u j) = if (0 : Fin 3) = j then 1 else 0)
    (h₂ : ∀ j k, ℓ₂ (t j k) = if (1 : Fin 3) = j ∧ (2 : Fin 3) = k then 1 else 0) :
    ((TensorProduct.lid ℂ ℂ).toLinearMap ∘ₗ TensorProduct.map ℓ₁ ℓ₂)
      (∑ i, ∑ j, ∑ k, (eps i j k • u i) ⊗ₜ[ℂ] t j k) = 1 := by
  simp [TensorProduct.map_tmul, h₁, h₂, Fin.sum_univ_three, eps]

end Raw

/-! ## The two singlet constructions -/

/-- **Trace-type singlet.** If `g` moves `u` by `M g` and `w` by `N g` with `M Nᵀ = 1`, then
`∑ᵢ uᵢ ⊗ wᵢ` is a nonzero invariant of `X ⊗ Y`. -/
noncomputable def singletPair {X Y : FDRep ℂ SU3} {M N : SU3 → Matrix (Fin 3) (Fin 3) ℂ}
    (F : Frame X M) (G : Frame Y N) (h : ∀ g, M g * (N g).transpose = 1) :
    Singlet (X ⊗ Y) where
  v := ∑ i, (F.u i ⊗ₜ[ℂ] G.u i : TensorProduct ℂ X Y)
  ℓ := pairFun (F.ℓ 0) (G.ℓ 0)
  inv g := by
    change TensorProduct.map (X.ρ g) (Y.ρ g) (∑ i, F.u i ⊗ₜ[ℂ] G.u i) = _
    exact pair_raw _ _ _ _ (fun a i => M g a i) (fun a i => N g a i) (F.moves g) (G.moves g)
      (fun a b => by rw [pair_contract, h g, Matrix.one_apply])
  coord := by
    change (TensorProduct.lid ℂ ℂ) (TensorProduct.map (F.ℓ 0) (G.ℓ 0)
      (∑ i, F.u i ⊗ₜ[ℂ] G.u i)) = 1
    simp [TensorProduct.map_tmul, F.coord, G.coord, Fin.sum_univ_three]

/-- Nine vectors `t j k` of `Q` (think `vⱼ ⊗ w_k`) that `g` moves by `M_{bj} M_{ck}`. -/
structure Frame2 (Q : FDRep ℂ SU3) (M : SU3 → Matrix (Fin 3) (Fin 3) ℂ) where
  t : Fin 3 → Fin 3 → Q
  ℓ : Fin 3 → Fin 3 → (Q →ₗ[ℂ] ℂ)
  moves : ∀ g j k, Q.ρ g (t j k) = ∑ b, ∑ c, (M g b j * M g c k) • t b c
  coord : ∀ j k j' k', ℓ j k (t j' k') = if j = j' ∧ k = k' then 1 else 0

/-- `vⱼ ⊗ w_k` in `Y ⊗ Z` from two frames moved by the same matrix. -/
noncomputable def frame2Tensor {Y Z : FDRep ℂ SU3} {M : SU3 → Matrix (Fin 3) (Fin 3) ℂ}
    (G : Frame Y M) (H : Frame Z M) : Frame2 (Y ⊗ Z) M where
  t j k := (G.u j ⊗ₜ[ℂ] H.u k : TensorProduct ℂ Y Z)
  ℓ j k := pairFun (G.ℓ j) (H.ℓ k)
  moves g j k := by
    change TensorProduct.map (Y.ρ g) (Z.ρ g) (G.u j ⊗ₜ[ℂ] H.u k) = _
    exact tmul_raw _ _ _ _ (fun a i => M g a i) (G.moves g) (H.moves g) j k
  coord j k j' k' := by
    rw [pairFun_tmul, G.coord, H.coord]
    split_ifs <;> simp_all

/-- The vector `∑ ε_{ijk} uᵢ ⊗ t_{jk}` of `X ⊗ Q`. -/
noncomputable def epsVec {X Q : FDRep ℂ SU3} {M : SU3 → Matrix (Fin 3) (Fin 3) ℂ}
    (F : Frame X M) (T : Frame2 Q M) : (X ⊗ Q : FDRep ℂ SU3) :=
  (∑ i, ∑ j, ∑ k, (eps i j k • F.u i) ⊗ₜ[ℂ] T.t j k : TensorProduct ℂ X Q)

theorem epsVec_inv {X Q : FDRep ℂ SU3} {M : SU3 → Matrix (Fin 3) (Fin 3) ℂ}
    (F : Frame X M) (T : Frame2 Q M) (h : ∀ g, (M g).det = 1) (g : SU3) :
    (X ⊗ Q).ρ g (epsVec F T) = epsVec F T := by
  have hc : ∀ a b c, ∑ i, ∑ j, ∑ k, eps i j k * (M g a i * (M g b j * M g c k)) =
      eps a b c := fun a b c => by rw [eps_contract, h g, one_mul]
  exact eps_raw (X.ρ g) (Q.ρ g) F.u T.t (fun a i => M g a i) (F.moves g) (T.moves g) hc

theorem epsVec_coord {X Q : FDRep ℂ SU3} {M : SU3 → Matrix (Fin 3) (Fin 3) ℂ}
    (F : Frame X M) (T : Frame2 Q M) : pairFun (F.ℓ 0) (T.ℓ 1 2) (epsVec F T) = 1 := by
  have h1 := F.coord 0
  have h2 := T.coord 1 2
  exact eps_coord_raw F.u T.t (F.ℓ 0) (T.ℓ 1 2) h1 h2

/-- **ε-type singlet.** If `g` moves `u` by `M g` and `t j k` by `M_{bj} M_{ck}`, with
`det (M g) = 1`, then `∑ ε_{ijk} uᵢ ⊗ t_{jk}` is a nonzero invariant of `X ⊗ Q`. -/
noncomputable def singletEps {X Q : FDRep ℂ SU3} {M : SU3 → Matrix (Fin 3) (Fin 3) ℂ}
    (F : Frame X M) (T : Frame2 Q M) (h : ∀ g, (M g).det = 1) : Singlet (X ⊗ Q) where
  v := epsVec F T
  ℓ := pairFun (F.ℓ 0) (T.ℓ 1 2)
  inv := epsVec_inv F T h
  coord := epsVec_coord F T

/-! ## The determinant and unitarity conditions for SU(3) -/

theorem det_eq_one (g : SU3) : g.1.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.1 g.2).2

/-- `g g⁻¹ = 1` read as `M Nᵀ = 1` for `M = g`, `N = (g⁻¹)ᵀ` (the pairing `3 ⊗ 3̄`). -/
theorem unitary_pair_fund (g : SU3) : g.1 * ((g⁻¹).1.transpose).transpose = 1 := by
  rw [Matrix.transpose_transpose, ← Submonoid.coe_mul, mul_inv_cancel]
  rfl

/-- The pairing `3̄ ⊗ 3`: `(g⁻¹)ᵀ gᵀ = (g g⁻¹)ᵀ = 1`. -/
theorem unitary_pair_antifund (g : SU3) : (g⁻¹).1.transpose * g.1.transpose = 1 := by
  rw [← Matrix.transpose_mul, ← Submonoid.coe_mul, mul_inv_cancel]
  simp

/-- `det (g⁻¹)ᵀ = 1`: the dual triple `3̄ ⊗ 3̄ ⊗ 3̄`. -/
theorem det_inv_transpose (g : SU3) : (g⁻¹).1.transpose.det = 1 := by
  rw [Matrix.det_transpose, det_eq_one]

/-! ## The three smallest invariants -/

/-- The trace singlet `∑ᵢ eᵢ ⊗ eᵢ*` of `3 ⊗ 3̄`. -/
noncomputable def singletTrace : Singlet (fund ⊗ antifund) :=
  singletPair frameFund frameAntifund unitary_pair_fund

/-- The ε singlet `∑ ε_{ijk} eᵢ ⊗ eⱼ ⊗ e_k` of `3 ⊗ 3 ⊗ 3`. -/
noncomputable def singletEps3 : Singlet (fund ⊗ (fund ⊗ fund)) :=
  singletEps frameFund (frame2Tensor frameFund frameFund) det_eq_one

/-- The dual ε singlet `∑ ε_{ijk} eᵢ* ⊗ eⱼ* ⊗ e_k*` of `3̄ ⊗ 3̄ ⊗ 3̄`. -/
noncomputable def singletEps3bar : Singlet (antifund ⊗ (antifund ⊗ antifund)) :=
  singletEps frameAntifund (frame2Tensor frameAntifund frameAntifund) det_inv_transpose

/-- The trace vector `∑ᵢ eᵢ ⊗ eᵢ* ∈ 3 ⊗ 3̄`. -/
noncomputable def traceVec : (fund ⊗ antifund : FDRep ℂ SU3) := singletTrace.v

/-- `ε = ∑ ε_{ijk} eᵢ ⊗ (eⱼ ⊗ e_k) ∈ 3 ⊗ 3 ⊗ 3`. -/
noncomputable def epsVec3 : (fund ⊗ (fund ⊗ fund) : FDRep ℂ SU3) := singletEps3.v

/-- `ε* = ∑ ε_{ijk} eᵢ* ⊗ (eⱼ* ⊗ e_k*) ∈ 3̄ ⊗ 3̄ ⊗ 3̄`. -/
noncomputable def epsVec3bar : (antifund ⊗ (antifund ⊗ antifund) : FDRep ℂ SU3) :=
  singletEps3bar.v

/-- `traceVec` is literally `∑ᵢ eᵢ ⊗ eᵢ*`. -/
theorem traceVec_eq : traceVec = (∑ i, ((Pi.single i 1 : Fin 3 → ℂ) ⊗ₜ[ℂ]
    (LinearMap.proj i : (Fin 3 → ℂ) →ₗ[ℂ] ℂ) : TensorProduct ℂ fund antifund)) := rfl

/-- `epsVec3` is literally `∑ ε_{ijk} eᵢ ⊗ (eⱼ ⊗ e_k)`. -/
theorem epsVec3_eq : epsVec3 = (∑ i, ∑ j, ∑ k, ((eps i j k • (Pi.single i 1 : Fin 3 → ℂ)) ⊗ₜ[ℂ]
    (((Pi.single j 1 : Fin 3 → ℂ) ⊗ₜ[ℂ] (Pi.single k 1 : Fin 3 → ℂ) :
      TensorProduct ℂ fund fund) : (fund ⊗ fund : FDRep ℂ SU3)) :
        TensorProduct ℂ fund (fund ⊗ fund : FDRep ℂ SU3))) := rfl

/-- **The trace invariant.** `g · ∑ᵢ eᵢ ⊗ eᵢ* = ∑ᵢ eᵢ ⊗ eᵢ*` for every `g ∈ SU(3)` (uses
`g g⁻¹ = 1`). -/
theorem traceVec_invariant (g : SU3) : (fund ⊗ antifund).ρ g traceVec = traceVec :=
  singletTrace.inv g

theorem traceVec_ne_zero : traceVec ≠ 0 := singletTrace.ne_zero

/-- **The ε invariant.** `g · ε = ε` for every `g ∈ SU(3)` (uses `det g = 1`). -/
theorem epsVec3_invariant (g : SU3) : (fund ⊗ (fund ⊗ fund)).ρ g epsVec3 = epsVec3 :=
  singletEps3.inv g

theorem epsVec3_ne_zero : epsVec3 ≠ 0 := singletEps3.ne_zero

/-- **The dual ε invariant.** `g · ε* = ε*` for every `g ∈ SU(3)` (uses
`det (g⁻¹)ᵀ = 1`; `(g⁻¹)ᵀ = conj g` for unitary `g`). -/
theorem epsVec3bar_invariant (g : SU3) :
    (antifund ⊗ (antifund ⊗ antifund)).ρ g epsVec3bar = epsVec3bar :=
  singletEps3bar.inv g

theorem epsVec3bar_ne_zero : epsVec3bar ≠ 0 := singletEps3bar.ne_zero

/-- `3 ⊗ 3̄` has a nonzero invariant. -/
theorem invariants_fund_antifund_ne_bot :
    Representation.invariants (fund ⊗ antifund).ρ ≠ ⊥ := singletTrace.invariants_ne_bot

/-- `3 ⊗ 3 ⊗ 3` has a nonzero invariant. -/
theorem invariants_fund3_ne_bot :
    Representation.invariants (fund ⊗ (fund ⊗ fund)).ρ ≠ ⊥ := singletEps3.invariants_ne_bot

/-- `3̄ ⊗ 3̄ ⊗ 3̄` has a nonzero invariant. -/
theorem invariants_antifund3_ne_bot :
    Representation.invariants (antifund ⊗ (antifund ⊗ antifund)).ρ ≠ ⊥ :=
  singletEps3bar.invariants_ne_bot

/-! ## Theta-graph vertices: the smallest table rows are attained

At the first theta vertex all three arms are outgoing, so the vertex space is
`A ⊗ (B ⊗ (C ⊗ 𝟙))` (`vertexRep`); at the second all are incoming, giving the duals.
The arm `(1, 0)` is carried by `3 = fund`, `(0, 1)` by `3̄ = antifund`, `(0, 0)` by `𝟙`. -/

/-- The unit representation. -/
noncomputable abbrev one : FDRep ℂ SU3 := 𝟙_ (FDRep ℂ SU3)

/-- The vertex with three arms of the given orientation. -/
noncomputable def thetaVertex (o : Bool) (A B C : FDRep ℂ SU3) : FDRep ℂ SU3 :=
  vertexRep [⟨A, o⟩, ⟨B, o⟩, ⟨C, o⟩]

section Builders

variable {U A B C : FDRep ℂ SU3} {M N : SU3 → Matrix (Fin 3) (Fin 3) ℂ}

/-- Pair singlet with the trivial arm first. -/
noncomputable def pairRow1 (s : Singlet U) (F : Frame A M) (G : Frame B N)
    (h : ∀ g, M g * (N g).transpose = 1) : Singlet (U ⊗ (A ⊗ (B ⊗ one))) :=
  singletTensor s (singletPair F (frameTensorSinglet G singletUnit) h)

/-- Pair singlet with the trivial arm second. -/
noncomputable def pairRow2 (s : Singlet U) (F : Frame A M) (G : Frame B N)
    (h : ∀ g, M g * (N g).transpose = 1) : Singlet (A ⊗ (U ⊗ (B ⊗ one))) :=
  singletPair F (singletTensorFrame s (frameTensorSinglet G singletUnit)) h

/-- Pair singlet with the trivial arm third. -/
noncomputable def pairRow3 (s : Singlet U) (F : Frame A M) (G : Frame B N)
    (h : ∀ g, M g * (N g).transpose = 1) : Singlet (A ⊗ (B ⊗ (U ⊗ one))) :=
  singletPair F (frameTensorSinglet G (singletTensor s singletUnit)) h

/-- ε singlet on three arms. -/
noncomputable def epsRow (F : Frame A M) (G : Frame B M) (H : Frame C M)
    (h : ∀ g, (M g).det = 1) : Singlet (A ⊗ (B ⊗ (C ⊗ one))) :=
  singletEps F (frame2Tensor G (frameTensorSinglet H singletUnit)) h

end Builders

/-- `3̄ᘁ` with the frame `ev(eᵢ)`, moved by `g`. -/
noncomputable def frameAntifundDual : Frame (antifund : FDRep ℂ SU3)ᘁ (fun g => g.1) :=
  frameDDual frameFund

/-- Row `(1, 3̄, 3)`: attained at both theta vertices. -/
theorem row_1_3bar_3 : ((0, 0), (0, 1), (1, 0)) ∈ thetaList ∧
    Representation.invariants (thetaVertex true one antifund fund).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false one antifund fund).ρ ≠ ⊥ :=
  ⟨by decide,
    (pairRow1 singletUnit frameAntifund frameFund unitary_pair_antifund).invariants_ne_bot,
    (pairRow1 singletUnitDual frameAntifundDual frameAntifund unitary_pair_fund).invariants_ne_bot⟩

/-- Row `(1, 3, 3̄)`. -/
theorem row_1_3_3bar : ((0, 0), (1, 0), (0, 1)) ∈ thetaList ∧
    Representation.invariants (thetaVertex true one fund antifund).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false one fund antifund).ρ ≠ ⊥ :=
  ⟨by decide,
    (pairRow1 singletUnit frameFund frameAntifund unitary_pair_fund).invariants_ne_bot,
    (pairRow1 singletUnitDual frameAntifund frameAntifundDual unitary_pair_antifund).invariants_ne_bot⟩

/-- Row `(3̄, 1, 3)`. -/
theorem row_3bar_1_3 : ((0, 1), (0, 0), (1, 0)) ∈ thetaList ∧
    Representation.invariants (thetaVertex true antifund one fund).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false antifund one fund).ρ ≠ ⊥ :=
  ⟨by decide,
    (pairRow2 singletUnit frameAntifund frameFund unitary_pair_antifund).invariants_ne_bot,
    (pairRow2 singletUnitDual frameAntifundDual frameAntifund unitary_pair_fund).invariants_ne_bot⟩

/-- Row `(3̄, 3, 1)`. -/
theorem row_3bar_3_1 : ((0, 1), (1, 0), (0, 0)) ∈ thetaList ∧
    Representation.invariants (thetaVertex true antifund fund one).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false antifund fund one).ρ ≠ ⊥ :=
  ⟨by decide,
    (pairRow3 singletUnit frameAntifund frameFund unitary_pair_antifund).invariants_ne_bot,
    (pairRow3 singletUnitDual frameAntifundDual frameAntifund unitary_pair_fund).invariants_ne_bot⟩

/-- Row `(3, 1, 3̄)`. -/
theorem row_3_1_3bar : ((1, 0), (0, 0), (0, 1)) ∈ thetaList ∧
    Representation.invariants (thetaVertex true fund one antifund).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false fund one antifund).ρ ≠ ⊥ :=
  ⟨by decide,
    (pairRow2 singletUnit frameFund frameAntifund unitary_pair_fund).invariants_ne_bot,
    (pairRow2 singletUnitDual frameAntifund frameAntifundDual unitary_pair_antifund).invariants_ne_bot⟩

/-- Row `(3, 3̄, 1)`. -/
theorem row_3_3bar_1 : ((1, 0), (0, 1), (0, 0)) ∈ thetaList ∧
    Representation.invariants (thetaVertex true fund antifund one).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false fund antifund one).ρ ≠ ⊥ :=
  ⟨by decide,
    (pairRow3 singletUnit frameFund frameAntifund unitary_pair_fund).invariants_ne_bot,
    (pairRow3 singletUnitDual frameAntifund frameAntifundDual unitary_pair_antifund).invariants_ne_bot⟩

/-- Row `(3, 3, 3)`: `ε` at the first vertex, `ε*` at the second. -/
theorem row_3_3_3 : ((1, 0), (1, 0), (1, 0)) ∈ thetaList ∧
    Representation.invariants (thetaVertex true fund fund fund).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false fund fund fund).ρ ≠ ⊥ :=
  ⟨by decide, (epsRow frameFund frameFund frameFund det_eq_one).invariants_ne_bot,
    (epsRow frameAntifund frameAntifund frameAntifund det_inv_transpose).invariants_ne_bot⟩

/-- Row `(3̄, 3̄, 3̄)`: `ε*` at the first vertex, `ε` (on `3̄ᘁ ≅ 3`) at the second. -/
theorem row_3bar_3bar_3bar : ((0, 1), (0, 1), (0, 1)) ∈ thetaList ∧
    Representation.invariants (thetaVertex true antifund antifund antifund).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false antifund antifund antifund).ρ ≠ ⊥ :=
  ⟨by decide,
    (epsRow frameAntifund frameAntifund frameAntifund det_inv_transpose).invariants_ne_bot,
    (epsRow frameAntifundDual frameAntifundDual frameAntifundDual det_eq_one).invariants_ne_bot⟩

/-- The eight rows of the theta table attained above. -/
def attainedRows : List (Irrep × Irrep × Irrep) :=
  [((0, 0), (0, 1), (1, 0)), ((0, 0), (1, 0), (0, 1)), ((0, 1), (0, 0), (1, 0)),
   ((0, 1), (1, 0), (0, 0)), ((1, 0), (0, 0), (0, 1)), ((1, 0), (0, 1), (0, 0)),
   ((1, 0), (1, 0), (1, 0)), ((0, 1), (0, 1), (0, 1))]

/-- They are exactly the rows of `thetaList` whose arms all lie in `{(0,0), (1,0), (0,1)}`. -/
theorem attainedRows_iff (t : Irrep × Irrep × Irrep) :
    t ∈ attainedRows ↔ t ∈ thetaList ∧ t.1 ∈ [(0, 0), (1, 0), (0, 1)] ∧
      t.2.1 ∈ [(0, 0), (1, 0), (0, 1)] ∧ t.2.2 ∈ [(0, 0), (1, 0), (0, 1)] := by
  constructor
  · intro h
    revert t
    decide
  · rintro ⟨h, h1, h2, h3⟩
    obtain ⟨a, b, c⟩ := t
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h2 h3
    rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;>
      rcases h3 with rfl | rfl | rfl <;> revert h <;> decide

/-! ## The control: `ε` is not invariant in `3 ⊗ 3 ⊗ 3̄` -/

/-- The nine vectors `eⱼ ⊗ e_k*` of `3 ⊗ 3̄`. -/
noncomputable def mixedT (j k : Fin 3) : (fund ⊗ antifund : FDRep ℂ SU3) :=
  (frameFund.u j ⊗ₜ[ℂ] frameAntifund.u k : TensorProduct ℂ fund antifund)

/-- `ε` with the same components `ε_{ijk}`, placed in `3 ⊗ (3 ⊗ 3̄)`. -/
noncomputable def epsMixed : (fund ⊗ (fund ⊗ antifund) : FDRep ℂ SU3) :=
  (∑ i, ∑ j, ∑ k, (eps i j k • frameFund.u i) ⊗ₜ[ℂ] mixedT j k :
    TensorProduct ℂ fund (fund ⊗ antifund : FDRep ℂ SU3))

theorem epsMixed_ne_zero : epsMixed ≠ 0 := by
  intro h0
  have h1 := eps_coord_raw frameFund.u mixedT (frameFund.ℓ 0)
    (pairFun (frameFund.ℓ 1) (frameAntifund.ℓ 2)) (frameFund.coord 0) (fun j k => by
      rw [mixedT, pairFun_tmul, frameFund.coord, frameAntifund.coord]
      split_ifs <;> simp_all)
  have h2 : pairFun (frameFund.ℓ 0) (pairFun (frameFund.ℓ 1) (frameAntifund.ℓ 2)) epsMixed = 1 :=
    h1
  rw [h0, map_zero] at h2
  exact zero_ne_one h2

/-- `ω·I` acts on `3 ⊗ (3 ⊗ 3̄)` by `ω · ω · ω² = ω`. -/
theorem centreActs_mixed : CentreActs zω ω (fund ⊗ (fund ⊗ antifund)) := by
  have h := centreActs_tensor centreActs_fund (centreActs_tensor centreActs_fund centreActs_antifund)
  have hω : ω * (ω * ω ^ 2) = ω := by
    calc ω * (ω * ω ^ 2) = ω ^ 3 * ω := by ring
      _ = ω := by rw [omega_cube, one_mul]
  rwa [hω] at h

theorem omega_ne_one : ω ≠ 1 := omega_primitive.ne_one (by norm_num)

/-- The centre element `ω·I` scales `ε ∈ 3 ⊗ 3 ⊗ 3̄` by `ω`. -/
theorem epsMixed_centre : (fund ⊗ (fund ⊗ antifund)).ρ zω epsMixed = ω • epsMixed :=
  centreActs_mixed epsMixed

/-- **`3 ⊗ 3 ⊗ 3̄` has no nonzero invariant at all** (its triality is `1 + 1 + 2 ≡ 1`). -/
theorem invariants_mixed_eq_bot : Representation.invariants (fund ⊗ (fund ⊗ antifund)).ρ = ⊥ := by
  by_contra h
  exact omega_ne_one (scalar_eq_one_of_invariant centreActs_mixed h)

/-- **`ε` is not SU(3)-invariant in `3 ⊗ 3 ⊗ 3̄`**: the negation of the false control. -/
theorem epsMixed_not_invariant :
    ¬ ∀ g : SU3, (fund ⊗ (fund ⊗ antifund)).ρ g epsMixed = epsMixed := by
  intro h
  have h1 := h zω
  rw [epsMixed_centre] at h1
  have h2 : (ω - 1) • epsMixed = 0 := by rw [sub_smul, one_smul, h1, sub_self]
  rcases smul_eq_zero.1 h2 with h3 | h3
  · exact omega_ne_one (sub_eq_zero.1 h3)
  · exact epsMixed_ne_zero h3

end SingletWitnessSU3
