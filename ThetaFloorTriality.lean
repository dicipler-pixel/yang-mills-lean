import IrrepEmbedSU3

/-!
# ThetaFloor's triality data from the proved SU(3) centre character

Author: Jeromie Beasley (Spectrum · Colour team lead, Grok Bot), with the Team.
ORCID https://orcid.org/0009-0006-4645-5643 · GitHub dicipler-pixel · X @d1c1pler ·
YouTube @AtlasMemoriae · atlas-memoriae.dicipler.workers.dev

`ThetaFloor` works with labels `Irrep := ℕ × ℕ`, the Casimir `cas3`, and a closed singlet
formula `hasSinglet` that is taken as a definition (cross-checked numerically, not derived).
`ThetaTriality` reads off `triality (p, q) = (p + 2q) % 3` and shows the `3 ∣ S₁` clause of
`hasSinglet` conserves it. `IrrepEmbedSU3` proves that the representation
`V(p, q) = irrepRep p q ⊆ 3^{⊗p} ⊗ 3̄^{⊗q}` has centre character `ω ^ ((p + 2q) mod 3)`
(`centreCharacter_irrep`). This file connects the two.

**Proved.**
* `triality_eq_exponent`, `irrep_centre_scalar`, `irrep_centre_exponent_unique`: the triality
  ThetaFloor/ThetaTriality attach to the label `(p, q)` is exactly the exponent by which
  `ω·I` acts on `V(p, q)`, and it is the only exponent in `{0, 1, 2}` that works.
* `irrep_swap_centre_iff`, `irrep10_not_triality_two`: giving `V(p, q)` the triality of the
  swapped label `(q, p)` is correct only when the triality is `0`; in particular `V(1, 0)`
  does not carry triality `2`.
* `singlet_clause_iff_out`, `singlet_clause_iff_in`, `hasSinglet_iff`: `hasSinglet` is
  exactly "the vertex triality vanishes" (the conclusion of the n-valent triality theorem, at
  either theta vertex) **and** the Bégin–Mathieu–Walton inequalities `bmw`.
* `singlet_clause_of_invariant_out`, `singlet_clause_of_invariant_in`: if the three arms are
  `V(a)`, `V(b)`, `V(c)` and the vertex space has a nonzero invariant, the triality clause of
  `hasSinglet` holds, by `nvalent_triality_irrepRep`. So that clause is proved from
  representation theory for the `V(p, q)` arms, at both vertices of the theta graph.
* `admissible_centre`, `not_admissible_of_out`, `not_admissible_of_in`, and the table lemmas
  `thetaList_centre`, `level40List_centre`, `level43List_centre`: every entry of the floor
  tables satisfies the proved centre-character condition at both vertices, and any labelling
  that violates it is excluded from the tables.
* `swap_one_arm_rejected`, `swap_entry_rejected`, `swap_entry_hasSinglet_false`: swapping
  `p ↔ q` on one arm of nonzero triality of an admissible labelling breaks the condition.
* `cas3_conj`, `cas3_mod_three`, `cas3_mod_three_eq_zero_iff`, `level3_mod_three`: how `cas3`
  meets triality. `cas3` is blind to `p ↔ q` (so only triality distinguishes `(p, q)` from
  `(q, p)` in the tables), and `cas3 (p, q) ≡ triality² (mod 3)`, so `C(p, q) = cas3 / 3` is an
  integer iff the triality is `0`, and `level = level3 / 3` is an integer iff the short arm has
  triality `0`.

**Not proved (open, named).**
* *Irreducibility of `V(p, q)`.* Without it, `cas3 (p, q)` is not shown to be the Casimir of
  `V(p, q)`; here `cas3` is a function of the label only, and the link above is label
  arithmetic. The same holds for the inequality part `bmw` of `hasSinglet`.
* *Classification:* that every irreducible SU(3) representation is some `V(p, q)`.
* The sufficiency direction: that the BMW inequalities plus vanishing triality give a nonzero
  invariant of `V(a) ⊗ V(b) ⊗ V(c)`.

No continuum or mass-gap statement is made.
-/

open CategoryTheory MonoidalCategory ThetaFloor ThetaTriality TrialityVertex GaugeSupport
  CentreCharacterSU3 IrrepEmbedSU3

namespace ThetaFloorTriality

/-! ## The triality label is the centre exponent of `V(p, q)` -/

/-- ThetaFloor's triality of the label `(p, q)` is the exponent `(p + 2q) % 3` of
`centreCharacter_irrep`. -/
theorem triality_eq_exponent (p q : ℕ) : triality (p, q) = (p + 2 * q) % 3 := rfl

/-- `ω·I` acts on `V(p, q)` by `ω ^ ((p + 2q) % 3)`. -/
theorem irrep_centre_scalar (p q : ℕ) :
    CentreActs zω (ω ^ ((p + 2 * q) % 3)) (irrepRep p q) :=
  centreCharacter_irrep p q

/-- The exponent is unique: if `ω·I` acts on `V(p, q)` by `ω ^ n` with `n < 3`, then `n` is
ThetaFloor's triality of `(p, q)`. -/
theorem irrep_centre_exponent_unique (p q n : ℕ) (hn : n < 3)
    (h : CentreActs zω (ω ^ n) (irrepRep p q)) : n = triality (p, q) := by
  have h1 := h (hwIrrep p q)
  rw [centreCharacter_irrep p q (hwIrrep p q)] at h1
  have hs : ω ^ triality (p, q) = ω ^ n := smul_left_injective ℂ (hwIrrep_ne_zero p q) h1
  exact (omega_primitive.pow_inj (Nat.mod_lt _ (by norm_num)) hn hs).symm

/-- Swapping the label: `V(p, q)` has the centre character of `(q, p)` iff its triality is 0. -/
theorem irrep_swap_centre_iff (p q : ℕ) :
    CentreCharacter zω ω (irrepRep p q) (q, p) ↔ triality (p, q) = 0 := by
  have hc := triality_conj (p, q)
  have hlt : triality (p, q) < 3 := Nat.mod_lt _ (by norm_num)
  have hlt' : triality (q, p) < 3 := Nat.mod_lt _ (by norm_num)
  simp only [conj] at hc
  constructor
  · intro h
    have := triality_eq_of_centreCharacter (hwIrrep p q) (hwIrrep_ne_zero p q)
      (centreCharacter_irrep p q) h
    omega
  · intro h
    have h' : triality (q, p) = triality (p, q) := by omega
    unfold CentreCharacter
    rw [h']
    exact centreCharacter_irrep p q

/-- `V(1, 0) = 3` does not carry triality `2` (the triality of the swapped label `(0, 1)`). -/
theorem irrep10_not_triality_two : ¬ CentreCharacter zω ω (irrepRep 1 0) (0, 1) := by
  rw [irrep_swap_centre_iff]
  decide

/-! ## `hasSinglet` = vanishing vertex triality + the BMW inequalities -/

/-- The inequality part of `hasSinglet` (everything except the `3 ∣ S₁` clause). -/
def bmw (a b c : Irrep) : Bool :=
  let P := a.1 + b.1 + c.1
  let Q := a.2 + b.2 + c.2
  let S1 := 2 * P + Q
  let S2 := P + 2 * Q
  let m := Nat.min S1 S2
  Nat.ble (3 * (a.1 + a.2)) m && Nat.ble (3 * (b.1 + b.2)) m && Nat.ble (3 * (c.1 + c.2)) m &&
  Nat.ble S1 (S2 + 3 * Nat.min a.1 (Nat.min b.1 c.1)) &&
  Nat.ble S2 (S1 + 3 * Nat.min a.2 (Nat.min b.2 c.2))

/-- The `3 ∣ S₁` clause is exactly the vanishing of the vertex triality, all arms outgoing
(first theta vertex). -/
theorem singlet_clause_iff_out (a b c : Irrep) :
    (2 * (a.1 + b.1 + c.1) + (a.2 + b.2 + c.2)) % 3 = 0 ↔
      vertexTri [(true, a), (true, b), (true, c)] = 0 := by
  obtain ⟨p1, q1⟩ := a
  obtain ⟨p2, q2⟩ := b
  obtain ⟨p3, q3⟩ := c
  simp only [vertexTri, armTri, triality, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, if_true]
  omega

/-- The same clause is the vanishing of the vertex triality with all arms incoming (second
theta vertex). -/
theorem singlet_clause_iff_in (a b c : Irrep) :
    (2 * (a.1 + b.1 + c.1) + (a.2 + b.2 + c.2)) % 3 = 0 ↔
      vertexTri [(false, a), (false, b), (false, c)] = 0 := by
  obtain ⟨p1, q1⟩ := a
  obtain ⟨p2, q2⟩ := b
  obtain ⟨p3, q3⟩ := c
  simp only [vertexTri, armTri, triality, conj, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Bool.false_eq_true, if_false]
  omega

/-- **`hasSinglet` splits** as the proved triality condition and the BMW inequalities. -/
theorem hasSinglet_iff (a b c : Irrep) :
    hasSinglet a b c = true ↔
      vertexTri [(true, a), (true, b), (true, c)] = 0 ∧ bmw a b c = true := by
  rw [← singlet_clause_iff_out]
  simp only [hasSinglet, bmw, Bool.and_eq_true, beq_iff_eq]
  tauto

/-! ## The triality clause from representation theory, for `V(p, q)` arms -/

/-- **First theta vertex.** Three outgoing arms `V(a)`, `V(b)`, `V(c)` with a nonzero vertex
invariant satisfy the triality clause of `hasSinglet` (by `nvalent_triality_irrepRep`). -/
theorem singlet_clause_of_invariant_out (h₁ h₂ h₃ : HalfEdge ℂ SU3) (a b c : Irrep)
    (r₁ : h₁.rep = irrepRep a.1 a.2) (r₂ : h₂.rep = irrepRep b.1 b.2)
    (r₃ : h₃.rep = irrepRep c.1 c.2) (o₁ : h₁.out = true) (o₂ : h₂.out = true)
    (o₃ : h₃.out = true) (hinv : Representation.invariants (vertexRep [h₁, h₂, h₃]).ρ ≠ ⊥) :
    (2 * (a.1 + b.1 + c.1) + (a.2 + b.2 + c.2)) % 3 = 0 := by
  have := nvalent_triality_irrepRep [(h₁, a), (h₂, b), (h₃, c)] (by simp [r₁, r₂, r₃]) hinv
  rw [singlet_clause_iff_out]
  simpa [o₁, o₂, o₃] using this

/-- **Second theta vertex.** The same with the three arms incoming. -/
theorem singlet_clause_of_invariant_in (h₁ h₂ h₃ : HalfEdge ℂ SU3) (a b c : Irrep)
    (r₁ : h₁.rep = irrepRep a.1 a.2) (r₂ : h₂.rep = irrepRep b.1 b.2)
    (r₃ : h₃.rep = irrepRep c.1 c.2) (o₁ : h₁.out = false) (o₂ : h₂.out = false)
    (o₃ : h₃.out = false) (hinv : Representation.invariants (vertexRep [h₁, h₂, h₃]).ρ ≠ ⊥) :
    (2 * (a.1 + b.1 + c.1) + (a.2 + b.2 + c.2)) % 3 = 0 := by
  have := nvalent_triality_irrepRep [(h₁, a), (h₂, b), (h₃, c)] (by simp [r₁, r₂, r₃]) hinv
  rw [singlet_clause_iff_in]
  simpa [o₁, o₂, o₃] using this

/-! ## The floor tables satisfy the proved condition -/

/-- An admissible labelling satisfies the centre-character condition at both theta vertices. -/
theorem admissible_centre (a b c : Irrep) (h : admissible a b c = true) :
    vertexTri [(true, a), (true, b), (true, c)] = 0 ∧
      vertexTri [(false, a), (false, b), (false, c)] = 0 := by
  have hs : hasSinglet a b c = true := by
    simp only [admissible, Bool.and_eq_true] at h
    exact h.1
  have h1 := ((hasSinglet_iff a b c).1 hs).1
  exact ⟨h1, (singlet_clause_iff_in a b c).1 ((singlet_clause_iff_out a b c).2 h1)⟩

/-- A labelling that violates the condition at the first vertex is not admissible. -/
theorem not_admissible_of_out (a b c : Irrep)
    (h : vertexTri [(true, a), (true, b), (true, c)] ≠ 0) : admissible a b c = false := by
  cases hA : admissible a b c
  · rfl
  · exact absurd (admissible_centre a b c hA).1 h

/-- A labelling that violates the condition at the second vertex is not admissible. -/
theorem not_admissible_of_in (a b c : Irrep)
    (h : vertexTri [(false, a), (false, b), (false, c)] ≠ 0) : admissible a b c = false := by
  cases hA : admissible a b c
  · rfl
  · exact absurd (admissible_centre a b c hA).2 h

/-- Every row of the 34-entry level ≤ 17 table satisfies the proved condition at both
vertices. -/
theorem thetaList_centre : ∀ t ∈ thetaList,
    vertexTri [(true, t.1), (true, t.2.1), (true, t.2.2)] = 0 ∧
      vertexTri [(false, t.1), (false, t.2.1), (false, t.2.2)] = 0 :=
  fun t ht => admissible_centre _ _ _ (thetaList_sound t ht).1

/-- The level 40/3 table satisfies it. -/
theorem level40List_centre : ∀ t ∈ level40List,
    vertexTri [(true, t.1), (true, t.2.1), (true, t.2.2)] = 0 ∧
      vertexTri [(false, t.1), (false, t.2.1), (false, t.2.2)] = 0 :=
  fun t ht => thetaList_centre t (level40List_sub t ht)

/-- The level 43/3 table satisfies it. -/
theorem level43List_centre : ∀ t ∈ level43List,
    vertexTri [(true, t.1), (true, t.2.1), (true, t.2.2)] = 0 ∧
      vertexTri [(false, t.1), (false, t.2.1), (false, t.2.2)] = 0 :=
  fun t ht => thetaList_centre t (level43List_sub t ht)

/-! ## Swapping `p ↔ q` on an arm breaks the condition -/

/-- Swapping `p ↔ q` on the second arm of an admissible labelling, when that arm has nonzero
triality, gives a nonzero vertex triality. -/
theorem swap_one_arm_rejected (a b c : Irrep) (h : admissible a b c = true)
    (hb : triality b ≠ 0) : vertexTri [(true, a), (true, conj b), (true, c)] ≠ 0 := by
  have h1 := (admissible_centre a b c h).1
  have hc := triality_conj b
  have hlt : triality b < 3 := Nat.mod_lt _ (by norm_num)
  simp only [vertexTri, armTri, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    if_true] at h1 ⊢
  omega

/-- The table row `((0,0), (0,1), (1,0))` (`1, 3̄, 3`) with the `3̄` arm swapped to `(1,0)`
fails the condition (total triality 2). -/
theorem swap_entry_rejected :
    ((0, 0), (0, 1), (1, 0)) ∈ thetaList ∧
      vertexTri [(true, (0, 0)), (true, conj (0, 1)), (true, (1, 0))] ≠ 0 := by decide

/-- ... and so is not a singlet. -/
theorem swap_entry_hasSinglet_false : hasSinglet (0, 0) (conj (0, 1)) (1, 0) = false := by
  decide

/-! ## How `cas3` meets triality -/

/-- `cas3` is symmetric under `p ↔ q`. -/
theorem cas3_conj (x : Irrep) : cas3 (conj x) = cas3 x := by
  obtain ⟨p, q⟩ := x
  simp only [cas3, conj]
  ring

/-- `cas3 (p, q) ≡ triality(p, q)² (mod 3)`. -/
theorem cas3_mod_three (x : Irrep) : cas3 x % 3 = (triality x * triality x) % 3 := by
  obtain ⟨p, q⟩ := x
  apply (ZMod.natCast_eq_natCast_iff' _ _ 3).1
  simp only [cas3, triality]
  push_cast
  rw [ZMod.natCast_mod]
  push_cast
  generalize (p : ZMod 3) = P
  generalize (q : ZMod 3) = Q
  revert P Q
  decide

/-- `C(p, q) = cas3 / 3` is an integer iff the triality is `0`. -/
theorem cas3_mod_three_eq_zero_iff (x : Irrep) : cas3 x % 3 = 0 ↔ triality x = 0 := by
  rw [cas3_mod_three]
  have hlt : triality x < 3 := Nat.mod_lt _ (by norm_num)
  generalize triality x = t at hlt ⊢
  interval_cases t <;> decide

/-- `level3 a b c ≡ triality(a)² (mod 3)`: the theta level is an integer iff the short arm has
triality `0`. -/
theorem level3_mod_three (a b c : Irrep) :
    level3 a b c % 3 = (triality a * triality a) % 3 := by
  rw [← cas3_mod_three]
  unfold level3
  omega

end ThetaFloorTriality
