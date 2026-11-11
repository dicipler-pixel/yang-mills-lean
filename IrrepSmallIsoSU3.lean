import SingletWitnessSU3

/-!
# `V(1, 0) ≅ 3`, `V(0, 1) ≅ 3̄`, `V(0, 0) ≅ 𝟙`

Author: Jeromie Beasley (Spectrum · Colour team lead, Grok Bot), with the Team.
ORCID https://orcid.org/0009-0006-4645-5643 · GitHub dicipler-pixel · X @d1c1pler ·
YouTube @AtlasMemoriae · atlas-memoriae.dicipler.workers.dev

`IrrepEmbedSU3` defines `V(p, q) = irrepRep p q` as the SU(3)-span of
`e₁^{⊗p} ⊗ e₃*^{⊗q}` inside `tensorRep p q = 3^{⊗p} ⊗ 3̄^{⊗q}` (right-nested, ending in `𝟙`).
`SingletWitnessSU3` builds its witnesses on `fund = 3`, `antifund = 3̄ = 3ᘁ` and `𝟙`. This file
identifies the two families for the three smallest labels, so that the witnesses and the
irrep embedding are statements about the same objects.

**The orbit spans.** `cyc` is the cyclic permutation matrix `e₀ ↦ e₁ ↦ e₂ ↦ e₀`; it is real
orthogonal with determinant `+1`, so it lies in SU(3) (`cyc_mem`).
* `cyc` moves `e₀ ↦ e₁ ↦ e₂` in `3` (`fund_cyc_e0`, `fund_cyc_e1`), so the orbit of `e₁` (the
  first basis vector `e₀` in `Fin 3` indexing) contains the whole standard basis.
* `cyc⁻¹` moves `e₂* ↦ e₁* ↦ e₀*` in `3̄` (`antifund_cycInv_proj2`, `antifund_cycInv_proj1`),
  so the orbit of `e₃*` contains the whole dual basis.
* `V(0, 0)` contains `1 ∈ ℂ = 𝟙`.

**Isomorphisms (FDRep isos).** The inclusion `irrepIncl` followed by the right unitor is a
bijective SU(3)-map, hence an iso:
* `irrep10Iso : irrepRep 1 0 ≅ fund`, sending `e₁ ⊗ 1 ↦ e₁` (`irrep10Iso_hw`);
* `irrep01Iso : irrepRep 0 1 ≅ antifund`, sending `e₃* ⊗ 1 ↦ e₃*` (`irrep01Iso_hw`);
* `irrep00Iso : irrepRep 0 0 ≅ 𝟙`, sending `1 ↦ 1` (`irrep00Iso_hw`).
Equivalently `irrepSub 1 0`, `irrepSub 0 1`, `irrepSub 0 0` are the whole tensor power
(`irrepSub10_eq_top`, `irrepSub01_eq_top`, `irrepSub00_eq_top`).

**The dual matters.** `irrep01_not_iso_fund`: `V(0, 1)` is not isomorphic to `3`, because
`ω·I` acts on `V(0, 1)` by `ω²` (`centreCharacter_irrep 0 1`) and on `3` by `ω`; hence also
`antifund_not_iso_fund` and `irrep10_not_iso_irrep01`. `FalseControls/IrrepDualControl.lean`
claims `V(0, 1) ≅ 3`.

**Witnesses transported.** With arms `V(1,0)`, `V(0,1)`, `V(0,0)`:
`irrep_trace_invariants_ne_bot` (`V(1,0) ⊗ V(0,1)`), `irrep_eps_invariants_ne_bot`
(`V(1,0)^{⊗3}`), `irrep_epsbar_invariants_ne_bot` (`V(0,1)^{⊗3}`), and
`attainedRows_irrep`: for each of the eight attained theta rows `(a, b, c)`, both theta
vertices with arms `V(a)`, `V(b)`, `V(c)` have a nonzero invariant. Together with
`nvalent_triality_irrepRep` this gives, for these rows, both directions of the singlet rule on
the same objects `V(p, q)`.

**Not proved (open).** Irreducibility of `V(p, q)` in general, the highest-weight
classification, and the identification of `V(p, q)` with a concrete model for larger labels.

No continuum or mass-gap statement is made.
-/

open CategoryTheory MonoidalCategory ThetaFloor ThetaTriality TrialityVertex GaugeSupport
  CentreCharacterSU3 IrrepEmbedSU3 SingletWitnessSU3

namespace IrrepSmallIsoSU3

/-! ## The cyclic permutation in SU(3) -/

/-- The cyclic permutation matrix `e₀ ↦ e₁ ↦ e₂ ↦ e₀` (columns are images). -/
def cycMat : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

/-- `cycMat` is unitary with determinant `1`. -/
theorem cyc_mem : cycMat ∈ SU3 := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cycMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply]
  · simp [cycMat, Matrix.det_fin_three]

/-- The cyclic permutation as an element of SU(3). -/
def cyc : SU3 := ⟨cycMat, cyc_mem⟩

/-- `cyc · e₀ = e₁` in `3`. -/
theorem fund_cyc_e0 : fund.ρ cyc (Pi.single 0 1 : Fin 3 → ℂ) = (Pi.single 1 1 : Fin 3 → ℂ) := by
  change Matrix.toLin' cycMat (Pi.single 0 1) = (Pi.single 1 1 : Fin 3 → ℂ)
  funext b
  fin_cases b <;> simp [cycMat, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- `cyc · e₁ = e₂` in `3`. -/
theorem fund_cyc_e1 : fund.ρ cyc (Pi.single 1 1 : Fin 3 → ℂ) = (Pi.single 2 1 : Fin 3 → ℂ) := by
  change Matrix.toLin' cycMat (Pi.single 1 1) = (Pi.single 2 1 : Fin 3 → ℂ)
  funext b
  fin_cases b <;> simp [cycMat, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- On `3̄`, `g⁻¹` sends the coordinate `xᵢ` to `x ↦ (g x)ᵢ`. -/
theorem antifund_inv_proj (g : SU3) (i : Fin 3) :
    antifund.ρ g⁻¹ (LinearMap.proj i : (Fin 3 → ℂ) →ₗ[ℂ] ℂ) =
      ((LinearMap.proj i : (Fin 3 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ Matrix.toLin' g.1 : (Fin 3 → ℂ) →ₗ[ℂ] ℂ) := by
  refine LinearMap.ext fun x => ?_
  refine (dual_ρ_apply fund g⁻¹ _ x).trans ?_
  rw [inv_inv]
  rfl

/-- `cyc⁻¹ · e₂* = e₁*` in `3̄`. -/
theorem antifund_cycInv_proj2 :
    antifund.ρ cyc⁻¹ (LinearMap.proj 2 : (Fin 3 → ℂ) →ₗ[ℂ] ℂ) =
      (LinearMap.proj 1 : (Fin 3 → ℂ) →ₗ[ℂ] ℂ) := by
  rw [antifund_inv_proj]
  refine LinearMap.ext fun x => ?_
  change (Matrix.toLin' cycMat x) 2 = x 1
  simp [cycMat, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- `cyc⁻¹ · e₁* = e₀*` in `3̄`. -/
theorem antifund_cycInv_proj1 :
    antifund.ρ cyc⁻¹ (LinearMap.proj 1 : (Fin 3 → ℂ) →ₗ[ℂ] ℂ) =
      (LinearMap.proj 0 : (Fin 3 → ℂ) →ₗ[ℂ] ℂ) := by
  rw [antifund_inv_proj]
  refine LinearMap.ext fun x => ?_
  change (Matrix.toLin' cycMat x) 1 = x 0
  simp [cycMat, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-! ## Orbit elements and a surjectivity criterion -/

theorem orbit_mem (p q : ℕ) (g : SU3) : (tensorRep p q).ρ g (hwVec p q) ∈ irrepSub p q :=
  Submodule.subset_span ⟨g, rfl⟩

/-- The orbit vector `g · (e₁^{⊗p} ⊗ e₃*^{⊗q})` as an element of `V(p, q)`. -/
noncomputable def orbitElt (p q : ℕ) (g : SU3) : irrepRep p q :=
  ⟨(tensorRep p q).ρ g (hwVec p q), orbit_mem p q g⟩

/-- A map out of `V(p, q)` whose image of the orbit contains a spanning set is surjective. -/
theorem surjective_of_orbit_span {p q : ℕ} {X : FDRep ℂ SU3} (f : irrepRep p q ⟶ X)
    (s : Set X) (hs : Submodule.span ℂ s = ⊤)
    (h : ∀ x ∈ s, ∃ g, f.hom.hom.hom (orbitElt p q g) = x) :
    Function.Surjective f.hom.hom.hom := by
  intro y
  have hle : Submodule.span ℂ s ≤ LinearMap.range f.hom.hom.hom := by
    refine Submodule.span_le.mpr ?_
    intro x hx
    obtain ⟨g, hg⟩ := h x hx
    exact ⟨_, hg⟩
  rw [hs] at hle
  exact hle Submodule.mem_top

theorem span_std_basis :
    Submodule.span ℂ (Set.range fun i : Fin 3 => (Pi.single i 1 : Fin 3 → ℂ)) = ⊤ := by
  have he : (fun i : Fin 3 => (Pi.single i 1 : Fin 3 → ℂ)) = ⇑(Pi.basisFun ℂ (Fin 3)) :=
    funext fun i => (Pi.basisFun_apply ℂ (Fin 3) i).symm
  rw [he]
  exact (Pi.basisFun ℂ (Fin 3)).span_eq

theorem span_dual_basis :
    Submodule.span ℂ (Set.range fun i : Fin 3 => (LinearMap.proj i : (Fin 3 → ℂ) →ₗ[ℂ] ℂ)) = ⊤ := by
  have h := ((Pi.basisFun ℂ (Fin 3)).dualBasis).span_eq
  have he : (fun i => (Pi.basisFun ℂ (Fin 3)).dualBasis i) =
      fun i : Fin 3 => (LinearMap.proj i : (Fin 3 → ℂ) →ₗ[ℂ] ℂ) := by
    funext i
    refine LinearMap.ext fun x => ?_
    simp
  rw [← he]
  exact h

/-- The right unitor `X ⊗ 𝟙 ⟶ X` sends `x ⊗ c` to `c • x`. -/
theorem rightUnitor_tmul (X : FDRep ℂ SU3) (x : X) (c : ℂ) :
    (ρ_ X).hom.hom.hom.hom (x ⊗ₜ[ℂ] c : TensorProduct ℂ X (𝟙_ (FDRep ℂ SU3))) = c • x :=
  ModuleCat.MonoidalCategory.rightUnitor_hom_apply x c

/-! ## `V(1, 0) ≅ 3` -/

/-- `V(1, 0) ⟶ 3 ⊗ 𝟙 ⟶ 3`. -/
noncomputable def f10 : irrepRep 1 0 ⟶ fund := irrepIncl 1 0 ≫ (ρ_ fund).hom

theorem f10_injective : Function.Injective f10.hom.hom.hom :=
  (GaugeSupport.injective_of_mono (ρ_ fund).hom).comp (GaugeSupport.injective_of_mono (irrepIncl 1 0))

theorem f10_orbit (g : SU3) : f10.hom.hom.hom (orbitElt 1 0 g) = fund.ρ g e1 := by
  change (ρ_ fund).hom.hom.hom.hom
    ((fund ⊗ 𝟙_ (FDRep ℂ SU3)).ρ g (e1 ⊗ₜ[ℂ] (1 : ℂ) : TensorProduct ℂ fund (𝟙_ (FDRep ℂ SU3)))) = _
  rw [tensor_ρ_tmul]
  exact (rightUnitor_tmul _ _ 1).trans (one_smul ℂ _)

theorem f10_bijective : Function.Bijective f10.hom.hom.hom := by
  refine ⟨f10_injective, surjective_of_orbit_span f10 _ span_std_basis ?_⟩
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · refine ⟨1, ?_⟩
    rw [f10_orbit, map_one, Module.End.one_apply]
    rfl
  · refine ⟨cyc, ?_⟩
    rw [f10_orbit]
    exact fund_cyc_e0
  · refine ⟨cyc * cyc, ?_⟩
    rw [f10_orbit, map_mul, Module.End.mul_apply]
    change fund.ρ cyc (fund.ρ cyc (Pi.single 0 1 : Fin 3 → ℂ)) = _
    rw [fund_cyc_e0, fund_cyc_e1]
    rfl

/-- **`V(1, 0) ≅ 3`.** -/
noncomputable def irrep10Iso : irrepRep 1 0 ≅ fund :=
  haveI := isIso_of_bijective f10 f10_bijective
  asIso f10

/-- The iso sends the highest-weight vector `e₁ ⊗ 1` to `e₁`. -/
theorem irrep10Iso_hw : irrep10Iso.hom.hom.hom.hom (hwIrrep 1 0) = e1 :=
  (rightUnitor_tmul fund e1 1).trans (one_smul ℂ _)

/-- `irrepSub 1 0` is all of `3 ⊗ 𝟙`. -/
theorem irrepSub10_eq_top : irrepSub 1 0 = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨w, hw⟩ := f10_bijective.2 ((ρ_ fund).hom.hom.hom.hom x)
  have hinj : Function.Injective (ρ_ fund).hom.hom.hom.hom :=
    GaugeSupport.injective_of_mono (ρ_ fund).hom
  have : (irrepIncl 1 0).hom.hom.hom w = x := hinj hw
  rw [← this]
  exact w.2

/-! ## `V(0, 1) ≅ 3̄` -/

/-- `V(0, 1) ⟶ 3̄ ⊗ 𝟙 ⟶ 3̄`. -/
noncomputable def f01 : irrepRep 0 1 ⟶ antifund := irrepIncl 0 1 ≫ (ρ_ antifund).hom

theorem f01_injective : Function.Injective f01.hom.hom.hom :=
  (GaugeSupport.injective_of_mono (ρ_ antifund).hom).comp (GaugeSupport.injective_of_mono (irrepIncl 0 1))

theorem f01_orbit (g : SU3) : f01.hom.hom.hom (orbitElt 0 1 g) = antifund.ρ g e3dual := by
  change (ρ_ antifund).hom.hom.hom.hom ((antifund ⊗ 𝟙_ (FDRep ℂ SU3)).ρ g
    (e3dual ⊗ₜ[ℂ] (1 : ℂ) : TensorProduct ℂ antifund (𝟙_ (FDRep ℂ SU3)))) = _
  rw [tensor_ρ_tmul]
  exact (rightUnitor_tmul _ _ 1).trans (one_smul ℂ _)

theorem f01_bijective : Function.Bijective f01.hom.hom.hom := by
  refine ⟨f01_injective, surjective_of_orbit_span f01 _ span_dual_basis ?_⟩
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · refine ⟨cyc⁻¹ * cyc⁻¹, ?_⟩
    rw [f01_orbit, map_mul, Module.End.mul_apply]
    change antifund.ρ cyc⁻¹ (antifund.ρ cyc⁻¹ (LinearMap.proj 2 : (Fin 3 → ℂ) →ₗ[ℂ] ℂ)) = _
    rw [antifund_cycInv_proj2, antifund_cycInv_proj1]
    rfl
  · refine ⟨cyc⁻¹, ?_⟩
    rw [f01_orbit]
    exact antifund_cycInv_proj2
  · refine ⟨1, ?_⟩
    rw [f01_orbit, map_one, Module.End.one_apply]
    rfl

/-- **`V(0, 1) ≅ 3̄`.** -/
noncomputable def irrep01Iso : irrepRep 0 1 ≅ antifund :=
  haveI := isIso_of_bijective f01 f01_bijective
  asIso f01

/-- The iso sends the highest-weight vector `e₃* ⊗ 1` to `e₃*`. -/
theorem irrep01Iso_hw : irrep01Iso.hom.hom.hom.hom (hwIrrep 0 1) = e3dual :=
  (rightUnitor_tmul antifund e3dual 1).trans (one_smul ℂ _)

/-- `irrepSub 0 1` is all of `3̄ ⊗ 𝟙`. -/
theorem irrepSub01_eq_top : irrepSub 0 1 = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨w, hw⟩ := f01_bijective.2 ((ρ_ antifund).hom.hom.hom.hom x)
  have hinj : Function.Injective (ρ_ antifund).hom.hom.hom.hom :=
    GaugeSupport.injective_of_mono (ρ_ antifund).hom
  have : (irrepIncl 0 1).hom.hom.hom w = x := hinj hw
  rw [← this]
  exact w.2

/-! ## `V(0, 0) ≅ 𝟙` -/

/-- `V(0, 0) ⟶ 𝟙` (here `tensorRep 0 0` is `𝟙` itself). -/
noncomputable def f00 : irrepRep 0 0 ⟶ 𝟙_ (FDRep ℂ SU3) := irrepIncl 0 0

instance mono_f00 : Mono f00 := mono_irrepIncl 0 0

theorem f00_bijective : Function.Bijective f00.hom.hom.hom := by
  refine ⟨GaugeSupport.injective_of_mono f00, ?_⟩
  intro y
  refine ⟨y • hwIrrep 0 0, ?_⟩
  rw [map_smul]
  exact mul_one (show ℂ from y)

/-- **`V(0, 0) ≅ 𝟙`.** -/
noncomputable def irrep00Iso : irrepRep 0 0 ≅ 𝟙_ (FDRep ℂ SU3) :=
  haveI := isIso_of_bijective f00 f00_bijective
  asIso f00

theorem irrep00Iso_hw : irrep00Iso.hom.hom.hom.hom (hwIrrep 0 0) = (1 : ℂ) := rfl

/-- `irrepSub 0 0` is all of `𝟙 = ℂ`. -/
theorem irrepSub00_eq_top : irrepSub 0 0 = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨w, hw⟩ := f00_bijective.2 x
  rw [← hw]
  exact w.2

/-! ## The dual matters: `V(0, 1) ≇ 3` -/

/-- **`V(0, 1)` is not isomorphic to `3`.** `ω·I` acts on `V(0, 1)` by `ω²` and on `3` by `ω`. -/
theorem irrep01_not_iso_fund : IsEmpty (irrepRep 0 1 ≅ fund) := by
  refine ⟨fun i => ?_⟩
  have h1 : CentreCharacter zω ω (irrepRep 0 1) (1, 0) :=
    centreActs_of_mono i.hom centreCharacter_fund
  have := triality_eq_of_centreCharacter (hwIrrep 0 1) (hwIrrep_ne_zero 0 1)
    (centreCharacter_irrep 0 1) h1
  simp [triality] at this

/-- Hence `3̄ ≇ 3`. -/
theorem antifund_not_iso_fund : IsEmpty (antifund ≅ fund) :=
  ⟨fun i => irrep01_not_iso_fund.false (irrep01Iso ≪≫ i)⟩

/-- And `V(1, 0) ≇ V(0, 1)`. -/
theorem irrep10_not_iso_irrep01 : IsEmpty (irrepRep 1 0 ≅ irrepRep 0 1) :=
  ⟨fun i => irrep01_not_iso_fund.false (i.symm ≪≫ irrep10Iso)⟩

/-! ## The witnesses on `V(1, 0)`, `V(0, 1)`, `V(0, 0)` -/

theorem invariants_ne_bot_of_iso {X Y : FDRep ℂ SU3} (i : X ≅ Y)
    (h : Representation.invariants Y.ρ ≠ ⊥) : Representation.invariants X.ρ ≠ ⊥ :=
  fun h0 => h ((invariants_eq_bot_iff_of_iso i).1 h0)

/-- **The trace singlet on `V(1, 0) ⊗ V(0, 1)`.** -/
theorem irrep_trace_invariants_ne_bot :
    Representation.invariants (irrepRep 1 0 ⊗ irrepRep 0 1).ρ ≠ ⊥ :=
  invariants_ne_bot_of_iso (irrep10Iso ⊗ᵢ irrep01Iso) invariants_fund_antifund_ne_bot

/-- **The ε singlet on `V(1, 0) ⊗ V(1, 0) ⊗ V(1, 0)`.** -/
theorem irrep_eps_invariants_ne_bot :
    Representation.invariants (irrepRep 1 0 ⊗ (irrepRep 1 0 ⊗ irrepRep 1 0)).ρ ≠ ⊥ :=
  invariants_ne_bot_of_iso (irrep10Iso ⊗ᵢ (irrep10Iso ⊗ᵢ irrep10Iso)) invariants_fund3_ne_bot

/-- **The dual ε singlet on `V(0, 1) ⊗ V(0, 1) ⊗ V(0, 1)`.** -/
theorem irrep_epsbar_invariants_ne_bot :
    Representation.invariants (irrepRep 0 1 ⊗ (irrepRep 0 1 ⊗ irrepRep 0 1)).ρ ≠ ⊥ :=
  invariants_ne_bot_of_iso (irrep01Iso ⊗ᵢ (irrep01Iso ⊗ᵢ irrep01Iso)) invariants_antifund3_ne_bot

/-- Isomorphic representations have isomorphic duals. -/
noncomputable def dualIso {X Y : FDRep ℂ SU3} (i : X ≅ Y) : Xᘁ ≅ Yᘁ :=
  letI : ExactPairing X Yᘁ := exactPairingCongrLeft i
  rightDualIso (inferInstance : ExactPairing X Xᘁ) this

/-- The factor of a half-edge with orientation `o` respects isomorphisms. -/
noncomputable def factorIso (o : Bool) {X Y : FDRep ℂ SU3} (i : X ≅ Y) :
    (⟨X, o⟩ : HalfEdge ℂ SU3).factor ≅ (⟨Y, o⟩ : HalfEdge ℂ SU3).factor := by
  cases o
  · rw [factor_in rfl, factor_in rfl]
    exact dualIso i
  · rw [factor_out rfl, factor_out rfl]
    exact i

/-- Theta vertices with isomorphic arms are isomorphic. -/
noncomputable def thetaVertexIso (o : Bool) {A B C A' B' C' : FDRep ℂ SU3} (a : A ≅ A')
    (b : B ≅ B') (c : C ≅ C') : thetaVertex o A B C ≅ thetaVertex o A' B' C' :=
  factorIso o a ⊗ᵢ (factorIso o b ⊗ᵢ (factorIso o c ⊗ᵢ Iso.refl _))

/-- The concrete model of the three smallest labels: `3`, `3̄`, `𝟙`. -/
noncomputable def smallRep : Irrep → FDRep ℂ SU3
  | (1, 0) => fund
  | (0, 1) => antifund
  | _ => one

/-- `V(x) ≅ smallRep x` for `x ∈ {(0,0), (1,0), (0,1)}`. -/
theorem irrep_iso_smallRep (x : Irrep) (hx : x ∈ [(0, 0), (1, 0), (0, 1)]) :
    Nonempty (irrepRep x.1 x.2 ≅ smallRep x) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨irrep00Iso⟩
  · exact ⟨irrep10Iso⟩
  · exact ⟨irrep01Iso⟩

/-- **The eight attained theta rows, on the arms `V(a)`, `V(b)`, `V(c)` themselves.** For
every row of `attainedRows`, both theta vertices (all arms outgoing / all incoming) with arms
`irrepRep` have a nonzero invariant. -/
theorem attainedRows_irrep (t : Irrep × Irrep × Irrep) (ht : t ∈ attainedRows) (o : Bool) :
    Representation.invariants (thetaVertex o (irrepRep t.1.1 t.1.2) (irrepRep t.2.1.1 t.2.1.2)
      (irrepRep t.2.2.1 t.2.2.2)).ρ ≠ ⊥ := by
  obtain ⟨_, h1, h2, h3⟩ := (attainedRows_iff t).1 ht
  obtain ⟨a⟩ := irrep_iso_smallRep _ h1
  obtain ⟨b⟩ := irrep_iso_smallRep _ h2
  obtain ⟨c⟩ := irrep_iso_smallRep _ h3
  refine invariants_ne_bot_of_iso (thetaVertexIso o a b c) ?_
  simp only [attainedRows, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases o
  · exact row_1_3bar_3.2.2
  · exact row_1_3bar_3.2.1
  · exact row_1_3_3bar.2.2
  · exact row_1_3_3bar.2.1
  · exact row_3bar_1_3.2.2
  · exact row_3bar_1_3.2.1
  · exact row_3bar_3_1.2.2
  · exact row_3bar_3_1.2.1
  · exact row_3_1_3bar.2.2
  · exact row_3_1_3bar.2.1
  · exact row_3_3bar_1.2.2
  · exact row_3_3bar_1.2.1
  · exact row_3_3_3.2.2
  · exact row_3_3_3.2.1
  · exact row_3bar_3bar_3bar.2.2
  · exact row_3bar_3bar_3bar.2.1

/-- **Both directions of the singlet rule on `V(p, q)` for the attained rows.** A row of
`attainedRows` is in the theta table, has vanishing vertex triality (as forced by
`nvalent_triality_irrepRep`) and has a nonzero invariant on the arms `V(a), V(b), V(c)` at both
theta vertices. -/
theorem attainedRows_irrep_both (t : Irrep × Irrep × Irrep) (ht : t ∈ attainedRows) :
    t ∈ thetaList ∧
    Representation.invariants (thetaVertex true (irrepRep t.1.1 t.1.2)
      (irrepRep t.2.1.1 t.2.1.2) (irrepRep t.2.2.1 t.2.2.2)).ρ ≠ ⊥ ∧
    Representation.invariants (thetaVertex false (irrepRep t.1.1 t.1.2)
      (irrepRep t.2.1.1 t.2.1.2) (irrepRep t.2.2.1 t.2.2.2)).ρ ≠ ⊥ :=
  ⟨((attainedRows_iff t).1 ht).1, attainedRows_irrep t ht true, attainedRows_irrep t ht false⟩

end IrrepSmallIsoSU3
