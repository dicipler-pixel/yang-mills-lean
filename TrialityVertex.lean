import DualSimple
import ThetaTriality
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Triality conservation at an n-valent vertex

Author: Jeromie Beasley (Lean Green PR Machine, Grok Bot), with the Team.
ORCID https://orcid.org/0009-0006-4645-5643 · GitHub dicipler-pixel · X @d1c1pler ·
YouTube @AtlasMemoriae · atlas-memoriae.dicipler.workers.dev

`CutFlux` (Spectrum) takes triality conservation at each vertex as its Gauss-law input, and
`ThetaTriality.singlet_triality` proves it only for trivalent vertices, from the closed
singlet formula of `ThetaFloor`. Here it is proved for a vertex of any valence `n`, from the
centre acting on each arm by `ω ^ triality`.

Setting, as in `GaugeSupportLattice`: a vertex is a list of half-edges `h`, each with a
representation `h.rep : FDRep k G` and an orientation (`out` contributes `h.rep`, `in`
contributes `h.repᘁ`). The vertex space is `vertexRep`, their right-nested tensor product.
Each arm also carries SU(3) Dynkin labels `(p, q)`, with `triality (p, q) = (p + 2q) % 3`,
which is `p − q` mod 3.

**Named hypothesis (not an axiom, not proved here):** `CentreCharacter z ω X x`, i.e. the
element `z` acts on `X` as the scalar `ω ^ triality x`. For SU(3), `z = ω·I` with `ω` a
primitive cube root of unity, and on the irrep with Dynkin labels `(p, q)` this is the
standard fact that the centre acts by `ω^(p − q)` (Schur plus the highest weight). It is not
in Mathlib v4.33.0, so every theorem below takes it as an explicit argument for each arm.
`CentreCharacterSU3.lean` proves it for `3`, `3̄`, `3^{⊗p} ⊗ 3̄^{⊗q}` and their subrepresentations
in Mathlib's `specialUnitaryGroup (Fin 3) ℂ`.

Proved here, for any group `G`, any element `z`, any field `k` and any `ω` with
`IsPrimitiveRoot ω 3`:
* `centreActs_unit`, `centreActs_tensor`, `centreActs_dual`: scalar actions multiply under
  `⊗`, invert under duals, and the unit has scalar `1`;
* `scalar_eq_one_of_invariant`: a nonzero invariant forces the scalar to be `1`;
* `nvalent_triality` (main): if each arm satisfies the named hypothesis and `vertexRep` has
  a nonzero invariant, then the signed trialities sum to `0` mod 3 (an incoming arm enters
  through `conj`, i.e. with a minus sign), for any valence;
* `nvalent_gauss`: the same as net triality flux `0` in `ZMod 3`, the form of `CutFlux.div`.
Low-valence corollaries: `one_valent_triality`, `two_valent_out_in`, `two_valent_out_out`,
`trivalent_triality`, plus `singlet_vertexTri`, which shows the closed singlet formula agrees
with the general rule.

Still open: the named hypothesis for genuine SU(3) irreps, and per-vertex nonvanishing of the
invariants (the regrouping and Peter–Weyl inputs of `GaugeSupportLattice`).
-/

open CategoryTheory MonoidalCategory ThetaFloor ThetaTriality

namespace TrialityVertex

/-! ## Labels: signed triality at a vertex -/

/-- Signed triality of an arm: `triality x` if it leaves the vertex, `triality (conj x)` if it
enters (that is `−triality x` mod 3). -/
def armTri (out : Bool) (x : Irrep) : Nat := if out then triality x else triality (conj x)

/-- Total signed triality at a vertex, mod 3 (`0` means conserved). -/
def vertexTri (arms : List (Bool × Irrep)) : Nat := (arms.map (fun a => armTri a.1 a.2)).sum % 3

/-- Triality in `ZMod 3`. -/
def triZ (x : Irrep) : ZMod 3 := (triality x : ZMod 3)

/-- Net triality leaving the vertex, in `ZMod 3` (outgoing minus incoming). -/
def netFlux (arms : List (Bool × Irrep)) : ZMod 3 :=
  (arms.map (fun a => if a.1 then triZ a.2 else -triZ a.2)).sum

theorem armTri_cast (out : Bool) (x : Irrep) :
    ((armTri out x : Nat) : ZMod 3) = if out then triZ x else -triZ x := by
  cases out
  · have h := triality_conj x
    simp only [armTri, triZ, Bool.false_eq_true, if_false]
    rw [eq_neg_iff_add_eq_zero, ← Nat.cast_add, ZMod.natCast_eq_zero_iff]
    omega
  · simp [armTri, triZ]

/-- Conservation mod 3 is the vanishing of the net flux in `ZMod 3`. -/
theorem vertexTri_eq_zero_iff (arms : List (Bool × Irrep)) :
    vertexTri arms = 0 ↔ netFlux arms = 0 := by
  have hc : (((arms.map (fun a => armTri a.1 a.2)).sum : Nat) : ZMod 3) = netFlux arms := by
    rw [Nat.cast_list_sum, List.map_map]
    unfold netFlux
    congr 1
    apply List.map_congr_left
    intro a _
    exact armTri_cast a.1 a.2
  rw [← hc, ZMod.natCast_eq_zero_iff, vertexTri, Nat.dvd_iff_mod_eq_zero]

/-! ## The centre acting by a scalar -/

section Rep

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G]

/-- `z` acts on `X` as the scalar `c`. -/
def CentreActs (z : G) (c : k) (X : FDRep k G) : Prop := ∀ v : X, X.ρ z v = c • v

/-- **Named hypothesis.** `z` acts on `X` by `ω ^ triality x`. For SU(3), `z = ω·I` and `X`
the irrep `(p, q)`; not proved here. -/
def CentreCharacter (z : G) (ω : k) (X : FDRep k G) (x : Irrep) : Prop :=
  CentreActs z (ω ^ triality x) X

theorem centreActs_unit (z : G) : CentreActs z (1 : k) (𝟙_ (FDRep k G)) := by
  intro v
  rw [one_smul]
  rfl

theorem centreActs_tensor {z : G} {c d : k} {X Y : FDRep k G} (hX : CentreActs z c X)
    (hY : CentreActs z d Y) : CentreActs z (c * d) (X ⊗ Y) := by
  intro v
  change TensorProduct.map (X.ρ z) (Y.ρ z) v = (c * d) • v
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [TensorProduct.map_tmul, hX x, hY y,
      TensorProduct.smul_tmul_smul]
  | add x y hx hy => rw [map_add, hx, hy, smul_add]

theorem centreActs_dual {z : G} {c c' : k} {X : FDRep k G} (hX : CentreActs z c X)
    (hc : c * c' = 1) : CentreActs z c' (Xᘁ) := by
  have hinv : ∀ x : X, X.ρ z⁻¹ x = c' • x := by
    intro x
    have h1 : X.ρ z (X.ρ z⁻¹ x) = x := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [hX] at h1
    calc X.ρ z⁻¹ x = (c' * c) • X.ρ z⁻¹ x := by rw [mul_comm, hc, one_smul]
      _ = c' • x := by rw [mul_smul, h1]
  intro φ
  change (show Module.Dual k X from (Xᘁ).ρ z φ) = c' • (show Module.Dual k X from φ)
  refine LinearMap.ext fun x => ?_
  refine (GaugeSupport.dual_ρ_apply X z φ x).trans ?_
  rw [hinv]
  exact LinearMap.map_smul (show Module.Dual k X from φ) c' x

/-- A nonzero invariant forces the scalar to be `1`. -/
theorem scalar_eq_one_of_invariant {z : G} {c : k} {X : FDRep k G} (hX : CentreActs z c X)
    (h : Representation.invariants X.ρ ≠ ⊥) : c = 1 := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  have h1 : c • v = (1 : k) • v := by rw [one_smul, ← hX v]; exact hv z
  exact smul_left_injective k hv0 h1

open GaugeSupport

/-- An arm satisfying the named hypothesis contributes the scalar `ω ^ armTri`. -/
theorem factor_centreActs {z : G} {ω : k} (hω : IsPrimitiveRoot ω 3) (h : HalfEdge k G)
    (x : Irrep) (hc : CentreCharacter z ω h.rep x) :
    CentreActs z (ω ^ armTri h.out x) h.factor := by
  unfold HalfEdge.factor armTri
  cases hout : h.out
  · simp only [Bool.false_eq_true, if_false]
    refine centreActs_dual hc ?_
    rw [← pow_add]
    exact (hω.pow_eq_one_iff_dvd _).2 (Nat.dvd_of_mod_eq_zero (triality_conj x))
  · simpa [CentreCharacter] using hc

/-- The whole vertex space acts by `ω ^ (sum of signed trialities)`. -/
theorem vertexRep_centreActs {z : G} {ω : k} (hω : IsPrimitiveRoot ω 3)
    (arms : List (HalfEdge k G × Irrep))
    (hcentre : ∀ a ∈ arms, CentreCharacter z ω a.1.rep a.2) :
    CentreActs z (ω ^ (arms.map (fun a => armTri a.1.out a.2)).sum)
      (vertexRep (arms.map Prod.fst)) := by
  induction arms with
  | nil =>
    simp only [List.map_nil, List.sum_nil, pow_zero]
    exact centreActs_unit z
  | cons a arms ih =>
    simp only [List.map_cons, List.sum_cons, pow_add]
    exact centreActs_tensor (factor_centreActs hω a.1 a.2 (hcentre a (by simp)))
      (ih (fun b hb => hcentre b (by simp [hb])))

/-- **Triality conservation at an n-valent vertex.** If the centre element `z` acts on
every arm by `ω ^ triality` (named hypothesis `CentreCharacter`) and the vertex space has a
nonzero invariant, then the signed trialities of the arms sum to `0` mod 3. Any valence. -/
theorem nvalent_triality {z : G} {ω : k} (hω : IsPrimitiveRoot ω 3)
    (arms : List (HalfEdge k G × Irrep))
    (hcentre : ∀ a ∈ arms, CentreCharacter z ω a.1.rep a.2)
    (hinv : Representation.invariants (vertexRep (arms.map Prod.fst)).ρ ≠ ⊥) :
    vertexTri (arms.map (fun a => (a.1.out, a.2))) = 0 := by
  have h1 := scalar_eq_one_of_invariant (vertexRep_centreActs hω arms hcentre) hinv
  rw [hω.pow_eq_one_iff_dvd] at h1
  unfold vertexTri
  rw [List.map_map]
  exact Nat.mod_eq_zero_of_dvd h1

/-- Gauss-law form: the net triality flux out of the vertex is `0` in `ZMod 3`. -/
theorem nvalent_gauss {z : G} {ω : k} (hω : IsPrimitiveRoot ω 3)
    (arms : List (HalfEdge k G × Irrep))
    (hcentre : ∀ a ∈ arms, CentreCharacter z ω a.1.rep a.2)
    (hinv : Representation.invariants (vertexRep (arms.map Prod.fst)).ρ ≠ ⊥) :
    netFlux (arms.map (fun a => (a.1.out, a.2))) = 0 :=
  (vertexTri_eq_zero_iff _).1 (nvalent_triality hω arms hcentre hinv)

/-! ## Low valence as corollaries -/

/-- One arm: a single arm of nonzero triality admits no nonzero invariant. -/
theorem one_valent_triality {z : G} {ω : k} (hω : IsPrimitiveRoot ω 3) (h : HalfEdge k G)
    (x : Irrep) (hc : CentreCharacter z ω h.rep x) (hx : triality x ≠ 0) :
    Representation.invariants (vertexRep [h]).ρ = ⊥ := by
  by_contra hinv
  have := nvalent_triality (z := z) hω [(h, x)] (by simpa using hc) hinv
  have h2 := triality_conj x
  have h3 : triality x < 3 := Nat.mod_lt _ (by decide)
  cases hout : h.out <;>
    simp [vertexTri, armTri, hout] at this <;> omega

/-- Two arms, one out and one in: equal trialities. -/
theorem two_valent_out_in {z : G} {ω : k} (hω : IsPrimitiveRoot ω 3) (h₁ h₂ : HalfEdge k G)
    (x y : Irrep) (c₁ : CentreCharacter z ω h₁.rep x) (c₂ : CentreCharacter z ω h₂.rep y)
    (o₁ : h₁.out = true) (o₂ : h₂.out = false)
    (hinv : Representation.invariants (vertexRep [h₁, h₂]).ρ ≠ ⊥) :
    triality x = triality y := by
  have := nvalent_triality (z := z) hω [(h₁, x), (h₂, y)] (by simp [c₁, c₂]) hinv
  have h2 := triality_conj y
  have h3 : triality x < 3 := Nat.mod_lt _ (by decide)
  have h4 : triality y < 3 := Nat.mod_lt _ (by decide)
  simp [vertexTri, armTri, o₁, o₂] at this
  omega

/-- Two arms, both out: the second carries the conjugate triality. -/
theorem two_valent_out_out {z : G} {ω : k} (hω : IsPrimitiveRoot ω 3) (h₁ h₂ : HalfEdge k G)
    (x y : Irrep) (c₁ : CentreCharacter z ω h₁.rep x) (c₂ : CentreCharacter z ω h₂.rep y)
    (o₁ : h₁.out = true) (o₂ : h₂.out = true)
    (hinv : Representation.invariants (vertexRep [h₁, h₂]).ρ ≠ ⊥) :
    triality y = triality (conj x) := by
  have := nvalent_triality (z := z) hω [(h₁, x), (h₂, y)] (by simp [c₁, c₂]) hinv
  have h2 := triality_conj x
  have h3 : triality (conj x) < 3 := Nat.mod_lt _ (by decide)
  have h4 : triality y < 3 := Nat.mod_lt _ (by decide)
  simp [vertexTri, armTri, o₁, o₂] at this
  omega

/-- Three outgoing arms: the conclusion of `ThetaTriality.singlet_triality`, now from the
centre character instead of the closed singlet formula. -/
theorem trivalent_triality {z : G} {ω : k} (hω : IsPrimitiveRoot ω 3) (h₁ h₂ h₃ : HalfEdge k G)
    (a b c : Irrep) (c₁ : CentreCharacter z ω h₁.rep a) (c₂ : CentreCharacter z ω h₂.rep b)
    (c₃ : CentreCharacter z ω h₃.rep c) (o₁ : h₁.out = true) (o₂ : h₂.out = true)
    (o₃ : h₃.out = true) (hinv : Representation.invariants (vertexRep [h₁, h₂, h₃]).ρ ≠ ⊥) :
    (triality a + triality b + triality c) % 3 = 0 := by
  have := nvalent_triality (z := z) hω [(h₁, a), (h₂, b), (h₃, c)] (by simp [c₁, c₂, c₃]) hinv
  simpa [vertexTri, armTri, o₁, o₂, o₃, Nat.add_assoc] using this

end Rep

/-! ## Agreement with the closed singlet formula, and checks -/

/-- The closed singlet formula of `ThetaFloor` obeys the general rule at a trivalent vertex. -/
theorem singlet_vertexTri (a b c : Irrep) (h : hasSinglet a b c = true) :
    vertexTri [(true, a), (true, b), (true, c)] = 0 := by
  have := singlet_triality a b c h
  simpa [vertexTri, armTri, Nat.add_assoc] using this

/-- Conserved: the baryon vertex `3 ⊗ 3 ⊗ 3`. -/
theorem baryon_conserved : vertexTri [(true, (1, 0)), (true, (1, 0)), (true, (1, 0))] = 0 := by
  decide

/-- Conserved: a meson line `3` in, `3` out. -/
theorem meson_conserved : vertexTri [(true, (1, 0)), (false, (1, 0))] = 0 := by decide

/-- Conserved at valence 5: `3, 3, 3̄, 8` out and `3` in. -/
theorem five_valent_conserved :
    vertexTri [(true, (1, 0)), (true, (1, 0)), (true, (0, 1)), (true, (1, 1)), (false, (1, 0))]
      = 0 := by decide

/-- Rejected: `3 ⊗ 3 ⊗ 1` (total triality 2). -/
theorem three_three_one_rejected : vertexTri [(true, (1, 0)), (true, (1, 0)), (true, (0, 0))] ≠ 0 := by
  decide

/-- Rejected: `3` out and `3̄` in (total triality 2). -/
theorem out_in_mismatch_rejected : vertexTri [(true, (1, 0)), (false, (0, 1))] ≠ 0 := by decide

end TrialityVertex
