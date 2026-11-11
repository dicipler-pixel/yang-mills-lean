import TrialityVertex
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The centre character of SU(3) on tensor-power representations

Author: Jeromie Beasley (Lean Green PR Machine, Grok Bot), with the Team.
ORCID https://orcid.org/0009-0006-4645-5643 · GitHub dicipler-pixel · X @d1c1pler ·
YouTube @AtlasMemoriae · atlas-memoriae.dicipler.workers.dev

`TrialityVertex` proves triality conservation at an n-valent vertex from the named hypothesis
`CentreCharacter z ω X x` (the element `z` acts on `X` by `ω ^ triality x`). Here that
hypothesis is proved for genuine SU(3) representations built from the defining one.

* `SU3 := Matrix.specialUnitaryGroup (Fin 3) ℂ`, `ω := exp(2πi/3)` (`omega_primitive`).
* `zω := ω • 1`, shown to lie in SU(3): unitary because `|ω| = 1`, and `det = ω³ = 1`.
* `fund`: the defining representation on `ℂ³`. `zω` acts by `ω = ω ^ triality (1, 0)`.
* `antifund := fundᘁ`: `zω` acts by `ω² = ω ^ triality (0, 1)`.
* `tensorRep p q := 3^{⊗p} ⊗ 3̄^{⊗q}`: `zω` acts by `ω ^ triality (p, q)`.
* Every subrepresentation, and more generally every `X` with a mono `X ⟶ tensorRep p q`, has
  the same centre character (`centreCharacter_of_mono`, `centreCharacter_subrep`).
* `nvalent_triality_SU3`: triality conservation at an n-valent vertex whose arms sit inside
  tensor-power representations, with no named hypothesis left.

**Boundary.** Mathlib v4.33.0 has no object "the irreducible SU(3) representation with
highest weight `(p, q)`". So the results are stated for the tensor representations
`3^{⊗p} ⊗ 3̄^{⊗q}` and for anything that embeds in them. The irrep `(p, q)` does sit inside
`3^{⊗p} ⊗ 3̄^{⊗q}` (its highest-weight vector is the tensor of highest-weight vectors), but
that embedding is classical representation theory and is not formalized here. An arm counts as
covered once a mono into some `tensorRep p q` is supplied. The label used is the one of the
tensor representation it embeds in.
-/

open CategoryTheory MonoidalCategory Complex ThetaFloor ThetaTriality TrialityVertex GaugeSupport

namespace CentreCharacterSU3

/-- SU(3) as Mathlib's special unitary group of `3 × 3` complex matrices. -/
abbrev SU3 := Matrix.specialUnitaryGroup (Fin 3) ℂ

/-- The primitive cube root of unity `exp(2πi/3)`. -/
noncomputable def ω : ℂ := exp (2 * Real.pi * I / 3)

theorem omega_primitive : IsPrimitiveRoot ω 3 := by
  have := isPrimitiveRoot_exp 3 (by norm_num)
  simpa [ω] using this

theorem omega_cube : ω ^ 3 = 1 := omega_primitive.pow_eq_one

theorem omega_mul_conj : ω * (starRingEnd ℂ) ω = 1 := by
  rw [mul_conj, normSq_eq_norm_sq]
  have h : ‖ω‖₊ = 1 := nnnorm_eq_one_of_pow_eq_one omega_cube (by norm_num)
  have h' : ‖ω‖ = 1 := by
    rw [← coe_nnnorm, h]; rfl
  rw [h']; norm_num

/-- `ω • 1` is a unitary matrix of determinant `ω³ = 1`, so it lies in SU(3). -/
theorem omega_smul_one_mem : (ω • (1 : Matrix (Fin 3) (Fin 3) ℂ)) ∈ SU3 := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [star_smul, star_one, smul_mul_smul_comm, one_mul]
    change (ω * (starRingEnd ℂ) ω) • (1 : Matrix (Fin 3) (Fin 3) ℂ) = 1
    rw [omega_mul_conj, one_smul]
  · rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one, omega_cube]

/-- The central element `ω·I` of SU(3). -/
noncomputable def zω : SU3 := ⟨ω • 1, omega_smul_one_mem⟩

/-- The defining representation of SU(3) on `ℂ³`. -/
noncomputable def fundRep : Representation ℂ SU3 (Fin 3 → ℂ) where
  toFun g := Matrix.toLin' g.1
  map_one' := by simp only [OneMemClass.coe_one, Matrix.toLin'_one]; rfl
  map_mul' g h := by
    simp only [Submonoid.coe_mul, Matrix.toLin'_mul]
    rfl

/-- The fundamental `3` as an object of `FDRep ℂ SU3`. -/
noncomputable def fund : FDRep ℂ SU3 := FDRep.of fundRep

/-- The antifundamental `3̄`, the dual of `3`. -/
noncomputable def antifund : FDRep ℂ SU3 := fundᘁ

/-- `ω·I` acts on `3` by `ω`. -/
theorem centreActs_fund : CentreActs zω ω fund := by
  intro v
  have key : ∀ w : Fin 3 → ℂ, Matrix.toLin' (ω • (1 : Matrix (Fin 3) (Fin 3) ℂ)) w = ω • w := by
    intro w
    rw [Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.one_mulVec]
  exact key v

/-- `3` has centre character `ω ^ triality (1, 0) = ω`. -/
theorem centreCharacter_fund : CentreCharacter zω ω fund (1, 0) := by
  unfold CentreCharacter
  simpa [triality] using centreActs_fund

/-- `ω·I` acts on `3̄` by `ω²`. -/
theorem centreActs_antifund : CentreActs zω (ω ^ 2) antifund :=
  centreActs_dual centreActs_fund (by rw [← pow_succ', omega_cube])

/-- `3̄` has centre character `ω ^ triality (0, 1) = ω²`. -/
theorem centreCharacter_antifund : CentreCharacter zω ω antifund (0, 1) := by
  unfold CentreCharacter
  simpa [triality] using centreActs_antifund

/-- Right-nested tensor product of a list in which each factor acts by a power of `ω`. -/
theorem centreActs_tensorList (l : List (FDRep ℂ SU3 × ℕ))
    (h : ∀ a ∈ l, CentreActs zω (ω ^ a.2) a.1) :
    CentreActs zω (ω ^ (l.map Prod.snd).sum) (tensorList (l.map Prod.fst)) := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.sum_nil, pow_zero]
    exact centreActs_unit zω
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, pow_add]
    exact centreActs_tensor (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

/-- The factors of `3^{⊗p} ⊗ 3̄^{⊗q}`, each with its exponent of `ω`. -/
noncomputable def tensorFactors (p q : ℕ) : List (FDRep ℂ SU3 × ℕ) :=
  List.replicate p (fund, 1) ++ List.replicate q (antifund, 2)

/-- The tensor representation `3^{⊗p} ⊗ 3̄^{⊗q}`. -/
noncomputable def tensorRep (p q : ℕ) : FDRep ℂ SU3 := tensorList ((tensorFactors p q).map Prod.fst)

theorem omega_pow_mod (n : ℕ) : ω ^ (n % 3) = ω ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, omega_cube, one_pow, one_mul]

/-- `ω·I` acts on `3^{⊗p} ⊗ 3̄^{⊗q}` by `ω ^ triality (p, q) = ω ^ ((p + 2q) mod 3)`. -/
theorem centreCharacter_tensorRep (p q : ℕ) : CentreCharacter zω ω (tensorRep p q) (p, q) := by
  have h := centreActs_tensorList (tensorFactors p q) (by
    intro a ha
    simp only [tensorFactors, List.mem_append, List.mem_replicate] at ha
    rcases ha with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · simpa using centreActs_fund
    · exact centreActs_antifund)
  have hs : ((tensorFactors p q).map Prod.snd).sum = p + 2 * q := by
    simp [tensorFactors, List.sum_replicate, mul_comm]
  rw [hs] at h
  unfold CentreCharacter
  rw [triality, omega_pow_mod]
  exact h

/-- A centre character passes to anything that maps injectively into the representation. -/
theorem centreActs_of_mono {G : Type} [Group G] {z : G} {c : ℂ} {X Y : FDRep ℂ G}
    (f : X ⟶ Y) [Mono f] (hY : CentreActs z c Y) : CentreActs z c X := by
  intro v
  apply injective_of_mono f
  have h := congrArg (fun m => m.hom.hom v) (f.comm z)
  change f.hom.hom.hom (X.ρ z v) = Y.ρ z (f.hom.hom.hom v) at h
  rw [h, hY, map_smul]

/-- Every representation embedded in `3^{⊗p} ⊗ 3̄^{⊗q}` has centre character
`ω ^ triality (p, q)`. -/
theorem centreCharacter_of_mono {X : FDRep ℂ SU3} {p q : ℕ} (f : X ⟶ tensorRep p q) [Mono f] :
    CentreCharacter zω ω X (p, q) :=
  centreActs_of_mono f (centreCharacter_tensorRep p q)

/-- Every subrepresentation of `3^{⊗p} ⊗ 3̄^{⊗q}` has centre character `ω ^ triality (p, q)`. -/
theorem centreCharacter_subrep (p q : ℕ) (W : Submodule ℂ (tensorRep p q))
    (hW : ∀ g, ∀ w ∈ W, (tensorRep p q).ρ g w ∈ W) :
    CentreCharacter zω ω (FDRep.of (Subrepresentation.toRepresentation
      (⟨W, fun g _ hw => hW g _ hw⟩ : Subrepresentation (tensorRep p q).ρ))) (p, q) := by
  have := mono_subIncl (tensorRep p q) W hW
  exact centreCharacter_of_mono (subIncl (tensorRep p q) W hW)

/-- The centre acts trivially on every subrepresentation of `3 ⊗ 3̄` (for instance the
adjoint `8`): triality `(1, 1)` is `0`. -/
theorem adjoint_centre_trivial {X : FDRep ℂ SU3} (f : X ⟶ tensorRep 1 1) [Mono f] :
    CentreActs zω 1 X := by
  have h := centreCharacter_of_mono f
  unfold CentreCharacter at h
  simpa [triality] using h

/-- **Unconditional n-valent triality conservation for SU(3).** At a vertex whose arms each
embed in some `3^{⊗p} ⊗ 3̄^{⊗q}`, labelled by that `(p, q)`, a nonzero invariant forces the
signed trialities to sum to `0` mod 3. No named hypothesis remains. -/
theorem nvalent_triality_SU3 (arms : List (HalfEdge ℂ SU3 × Irrep))
    (hsub : ∀ a ∈ arms, ∃ f : a.1.rep ⟶ tensorRep a.2.1 a.2.2, Mono f)
    (hinv : Representation.invariants (vertexRep (arms.map Prod.fst)).ρ ≠ ⊥) :
    vertexTri (arms.map (fun a => (a.1.out, a.2))) = 0 := by
  refine nvalent_triality (z := zω) omega_primitive arms (fun a ha => ?_) hinv
  obtain ⟨f, hf⟩ := hsub a ha
  exact centreCharacter_of_mono f

/-- The same for arms that are exactly tensor representations. -/
theorem nvalent_triality_tensorRep (arms : List (HalfEdge ℂ SU3 × Irrep))
    (hrep : ∀ a ∈ arms, a.1.rep = tensorRep a.2.1 a.2.2)
    (hinv : Representation.invariants (vertexRep (arms.map Prod.fst)).ρ ≠ ⊥) :
    vertexTri (arms.map (fun a => (a.1.out, a.2))) = 0 :=
  nvalent_triality_SU3 arms (fun a ha => ⟨eqToHom (hrep a ha), inferInstance⟩) hinv

end CentreCharacterSU3
