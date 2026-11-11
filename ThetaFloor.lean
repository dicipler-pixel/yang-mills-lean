/-!
# ThetaFloor: the SU(3) level list on the theta graph (core Lean, no Mathlib)

The theta graph is two adjacent plaquettes: two trivalent vertices joined by three
arms of 1, 3 and 3 links. A labelling `(a, b, c)` puts an SU(3) irrep on each arm
(`a` on the short arm, `b`, `c` on the long arms), irreps written as Dynkin labels
`(p, q)`. All three arms are oriented the same way between the two vertices, so the
vertex rule is: `a ⊗ b ⊗ c` contains the singlet (at the other vertex the conjugate
condition, which is equivalent). This matches `theta.py`, which tests
`conj c ∈ a ⊗ b`.

Levels are multiplied by 3 so everything is a natural number:
`cas3 (p, q) = p² + q² + pq + 3p + 3q = 3·C(p, q)` and
`level3 a b c = cas3 a + 3·cas3 b + 3·cas3 c = 3·level`.

**Scope of the tensor rule.** `hasSinglet` is the closed-form SU(3) invariant rule
(triality plus the Bégin–Mathieu–Walton / Berenstein–Zelevinsky inequalities):
with `S₁ = 2Σp + Σq`, `S₂ = Σp + 2Σq`, a singlet exists iff `3 ∣ S₁`,
`3(pᵢ + qᵢ) ≤ min S₁ S₂` for every arm, `S₁ ≤ S₂ + 3·min pᵢ` and `S₂ ≤ S₁ + 3·min qᵢ`.
This formula is NOT derived from representation theory in Lean. It is taken as the
definition here and was cross-checked numerically (`crosscheck.py`) against an
independent brute-force character computation (Gelfand–Tsetlin weight multisets and
dominant-weight peeling) for all 21952 triples with `p + q ≤ 6`, with zero
disagreements (the BMW multiplicity also matches exactly), and against `theta.py`'s
Racah–Speiser `tensor`, again with zero disagreements.

Everything after the definition is proved in the kernel: the cutoff lemmas by
arithmetic, the finite enumeration by `decide` (no `native_decide`, no `sorry`).
-/

namespace ThetaFloor

/-- An SU(3) irrep as Dynkin labels `(p, q)`. -/
abbrev Irrep := Nat × Nat

/-- `3 · C(p,q)`, three times the quadratic Casimir. -/
def cas3 (x : Irrep) : Nat := x.1 * x.1 + x.2 * x.2 + x.1 * x.2 + 3 * x.1 + 3 * x.2

/-- `3 · level` of the labelling: short arm weight 1, long arms weight 3. -/
def level3 (a b c : Irrep) : Nat := cas3 a + 3 * cas3 b + 3 * cas3 c

/-- Closed-form SU(3) singlet rule for `a ⊗ b ⊗ c` (see the module docstring). -/
def hasSinglet (a b c : Irrep) : Bool :=
  let P := a.1 + b.1 + c.1
  let Q := a.2 + b.2 + c.2
  let S1 := 2 * P + Q
  let S2 := P + 2 * Q
  let m := Nat.min S1 S2
  S1 % 3 == 0 &&
  Nat.ble (3 * (a.1 + a.2)) m && Nat.ble (3 * (b.1 + b.2)) m && Nat.ble (3 * (c.1 + c.2)) m &&
  Nat.ble S1 (S2 + 3 * Nat.min a.1 (Nat.min b.1 c.1)) &&
  Nat.ble S2 (S1 + 3 * Nat.min a.2 (Nat.min b.2 c.2))

/-- Admissible: both vertices carry a singlet and the labelling is not all-trivial. -/
def admissible (a b c : Irrep) : Bool :=
  hasSinglet a b c && !((a, b, c) == ((0, 0), (0, 0), (0, 0)))

/-- The 34 admissible labellings with level ≤ 17, exactly the rows of `theta.out`. -/
def thetaList : List (Irrep × Irrep × Irrep) :=
  [((0, 0), (0, 1), (1, 0)), ((0, 0), (1, 0), (0, 1)), ((0, 1), (0, 0), (1, 0)),
   ((0, 1), (0, 1), (0, 1)), ((0, 1), (0, 1), (2, 0)), ((0, 1), (1, 0), (0, 0)),
   ((0, 1), (1, 0), (1, 1)), ((0, 1), (1, 1), (1, 0)), ((0, 1), (2, 0), (0, 1)),
   ((0, 2), (0, 0), (2, 0)), ((0, 2), (0, 1), (1, 1)), ((0, 2), (1, 0), (1, 0)),
   ((0, 2), (1, 1), (0, 1)), ((0, 2), (2, 0), (0, 0)), ((1, 0), (0, 0), (0, 1)),
   ((1, 0), (0, 1), (0, 0)), ((1, 0), (0, 1), (1, 1)), ((1, 0), (0, 2), (1, 0)),
   ((1, 0), (1, 0), (0, 2)), ((1, 0), (1, 0), (1, 0)), ((1, 0), (1, 1), (0, 1)),
   ((1, 1), (0, 0), (1, 1)), ((1, 1), (0, 1), (0, 2)), ((1, 1), (0, 1), (1, 0)),
   ((1, 1), (0, 2), (0, 1)), ((1, 1), (1, 0), (0, 1)), ((1, 1), (1, 0), (2, 0)),
   ((1, 1), (1, 1), (0, 0)), ((1, 1), (2, 0), (1, 0)), ((2, 0), (0, 0), (0, 2)),
   ((2, 0), (0, 1), (0, 1)), ((2, 0), (0, 2), (0, 0)), ((2, 0), (1, 0), (1, 1)),
   ((2, 0), (1, 1), (1, 0))]

/-- The four labellings at level 40/3 (sextet square: `6` and `6̄` on the short arm
and one long arm, trivial on the other). -/
def level40List : List (Irrep × Irrep × Irrep) :=
  [((0, 2), (0, 0), (2, 0)), ((0, 2), (2, 0), (0, 0)),
   ((2, 0), (0, 0), (0, 2)), ((2, 0), (0, 2), (0, 0))]

/-- The four labellings at level 43/3 (`3` or `3̄` on the short arm, its conjugate on
one long arm, the octet on the other). -/
def level43List : List (Irrep × Irrep × Irrep) :=
  [((0, 1), (1, 0), (1, 1)), ((0, 1), (1, 1), (1, 0)),
   ((1, 0), (0, 1), (1, 1)), ((1, 0), (1, 1), (0, 1))]

/-- The ordered list of `3 · level` values ≤ 51:
16/3, 8, 28/3, 11, 34/3, 12, 40/3, 43/3, 46/3, 49/3, 17. -/
def levelSet3 : List Nat := [16, 24, 28, 33, 34, 36, 40, 43, 46, 49, 51]

/-! ## Cutoff lemmas -/

theorem cas3_ge_of_large (x : Irrep) (h : 7 ≤ x.1 + x.2) : 52 ≤ cas3 x := by
  obtain ⟨p, q⟩ := x
  simp only at h
  unfold cas3
  simp only
  by_cases hp : 7 ≤ p
  · have : 7 * p ≤ p * p := Nat.mul_le_mul_right p hp
    omega
  · by_cases hq : 7 ≤ q
    · have : 7 * q ≤ q * q := Nat.mul_le_mul_right q hq
      omega
    · have key : ∀ p < 7, ∀ q < 7, 7 ≤ p + q →
          52 ≤ p * p + q * q + p * q + 3 * p + 3 * q := by decide
      exact key p (by omega) q (by omega) h

theorem cas3_ge_of_mid (x : Irrep) (h : 4 ≤ x.1 + x.2) : 18 ≤ cas3 x := by
  obtain ⟨p, q⟩ := x
  simp only at h
  unfold cas3
  simp only
  by_cases hp : 4 ≤ p
  · have : 4 * p ≤ p * p := Nat.mul_le_mul_right p hp
    omega
  · by_cases hq : 4 ≤ q
    · have : 4 * q ≤ q * q := Nat.mul_le_mul_right q hq
      omega
    · have key : ∀ p < 4, ∀ q < 4, 4 ≤ p + q →
          18 ≤ p * p + q * q + p * q + 3 * p + 3 * q := by decide
      exact key p (by omega) q (by omega) h

/-- Cutoff: if any arm has `p + q ≥ 7`, then `3·level > 51`. -/
theorem cutoff_any_arm (a b c : Irrep)
    (h : 7 ≤ a.1 + a.2 ∨ 7 ≤ b.1 + b.2 ∨ 7 ≤ c.1 + c.2) : 51 < level3 a b c := by
  unfold level3
  rcases h with h | h | h
  · have := cas3_ge_of_large a h; omega
  · have := cas3_ge_of_large b h; omega
  · have := cas3_ge_of_large c h; omega

/-- Sharper cutoff for the long arms: `p + q ≥ 4` on a long arm forces `3·level > 51`. -/
theorem cutoff_long_arm (a b c : Irrep)
    (h : 4 ≤ b.1 + b.2 ∨ 4 ≤ c.1 + c.2) : 51 < level3 a b c := by
  unfold level3
  rcases h with h | h
  · have := cas3_ge_of_mid b h; omega
  · have := cas3_ge_of_mid c h; omega

/-- Hence level ≤ 17 confines the short arm to `p + q ≤ 6`, the long arms to `p + q ≤ 3`. -/
theorem bounds_of_level (a b c : Irrep) (h : level3 a b c ≤ 51) :
    a.1 + a.2 ≤ 6 ∧ b.1 + b.2 ≤ 3 ∧ c.1 + c.2 ≤ 3 := by
  refine ⟨?_, ?_, ?_⟩
  · apply Nat.le_of_not_lt; intro h'
    have := cutoff_any_arm a b c (Or.inl h'); omega
  · apply Nat.le_of_not_lt; intro h'
    have := cutoff_long_arm a b c (Or.inl h'); omega
  · apply Nat.le_of_not_lt; intro h'
    have := cutoff_long_arm a b c (Or.inr h'); omega

/-! ## Finite enumeration (split by the short arm's `p` to keep each `decide` small) -/

/-- The predicate checked on the finite box. -/
def good (a b c : Irrep) : Prop :=
  (admissible a b c = true ∧ level3 a b c ≤ 51) ↔ (a, b, c) ∈ thetaList

instance (a b c : Irrep) : Decidable (good a b c) := by unfold good; infer_instance

theorem box_p0 : ∀ q1 < 7, ∀ p2 < 4, ∀ q2 < 4, ∀ p3 < 4, ∀ q3 < 4,
    good (0, q1) (p2, q2) (p3, q3) := by decide +kernel
theorem box_p1 : ∀ q1 < 7, ∀ p2 < 4, ∀ q2 < 4, ∀ p3 < 4, ∀ q3 < 4,
    good (1, q1) (p2, q2) (p3, q3) := by decide +kernel
theorem box_p2 : ∀ q1 < 7, ∀ p2 < 4, ∀ q2 < 4, ∀ p3 < 4, ∀ q3 < 4,
    good (2, q1) (p2, q2) (p3, q3) := by decide +kernel
theorem box_p3 : ∀ q1 < 7, ∀ p2 < 4, ∀ q2 < 4, ∀ p3 < 4, ∀ q3 < 4,
    good (3, q1) (p2, q2) (p3, q3) := by decide +kernel
theorem box_p4 : ∀ q1 < 7, ∀ p2 < 4, ∀ q2 < 4, ∀ p3 < 4, ∀ q3 < 4,
    good (4, q1) (p2, q2) (p3, q3) := by decide +kernel
theorem box_p5 : ∀ q1 < 7, ∀ p2 < 4, ∀ q2 < 4, ∀ p3 < 4, ∀ q3 < 4,
    good (5, q1) (p2, q2) (p3, q3) := by decide +kernel
theorem box_p6 : ∀ q1 < 7, ∀ p2 < 4, ∀ q2 < 4, ∀ p3 < 4, ∀ q3 < 4,
    good (6, q1) (p2, q2) (p3, q3) := by decide +kernel

theorem good_of_box (a b c : Irrep) (ha : a.1 + a.2 ≤ 6) (hb : b.1 + b.2 ≤ 3)
    (hc : c.1 + c.2 ≤ 3) : good a b c := by
  obtain ⟨p1, q1⟩ := a
  obtain ⟨p2, q2⟩ := b
  obtain ⟨p3, q3⟩ := c
  simp only at ha hb hc
  have h1 : q1 < 7 := by omega
  have h2 : p2 < 4 := by omega
  have h3 : q2 < 4 := by omega
  have h4 : p3 < 4 := by omega
  have h5 : q3 < 4 := by omega
  have hp : p1 = 0 ∨ p1 = 1 ∨ p1 = 2 ∨ p1 = 3 ∨ p1 = 4 ∨ p1 = 5 ∨ p1 = 6 := by omega
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact box_p0 q1 h1 p2 h2 q2 h3 p3 h4 q3 h5
  · exact box_p1 q1 h1 p2 h2 q2 h3 p3 h4 q3 h5
  · exact box_p2 q1 h1 p2 h2 q2 h3 p3 h4 q3 h5
  · exact box_p3 q1 h1 p2 h2 q2 h3 p3 h4 q3 h5
  · exact box_p4 q1 h1 p2 h2 q2 h3 p3 h4 q3 h5
  · exact box_p5 q1 h1 p2 h2 q2 h3 p3 h4 q3 h5
  · exact box_p6 q1 h1 p2 h2 q2 h3 p3 h4 q3 h5

/-- Every listed labelling is admissible with level ≤ 17. -/
theorem thetaList_sound : ∀ t ∈ thetaList,
    admissible t.1 t.2.1 t.2.2 = true ∧ level3 t.1 t.2.1 t.2.2 ≤ 51 := by decide

/-! ## Main theorems -/

/-- **Enumeration.** A labelling is admissible with level ≤ 17 iff it is one of the
34 rows of `theta.out`. -/
theorem theta_enumeration (a b c : Irrep) :
    (admissible a b c = true ∧ level3 a b c ≤ 51) ↔ (a, b, c) ∈ thetaList := by
  constructor
  · intro h
    obtain ⟨hb1, hb2, hb3⟩ := bounds_of_level a b c h.2
    exact (good_of_box a b c hb1 hb2 hb3).1 h
  · intro h
    exact thetaList_sound (a, b, c) h

theorem thetaList_length : thetaList.length = 34 := by decide

theorem level40_char : ∀ t ∈ thetaList, level3 t.1 t.2.1 t.2.2 = 40 ↔ t ∈ level40List := by
  decide

theorem level43_char : ∀ t ∈ thetaList, level3 t.1 t.2.1 t.2.2 = 43 ↔ t ∈ level43List := by
  decide

theorem level40List_sub : ∀ t ∈ level40List, t ∈ thetaList := by decide
theorem level43List_sub : ∀ t ∈ level43List, t ∈ thetaList := by decide

/-- **Level 40/3** is realized by exactly the four sextet labellings. -/
theorem theta_level_40_3_iff (a b c : Irrep) :
    (admissible a b c = true ∧ level3 a b c = 40) ↔ (a, b, c) ∈ level40List := by
  constructor
  · intro ⟨ha, hl⟩
    have hm := (theta_enumeration a b c).1 ⟨ha, by omega⟩
    exact (level40_char _ hm).1 hl
  · intro h
    have hm := level40List_sub _ h
    exact ⟨((theta_enumeration a b c).2 hm).1, (level40_char _ hm).2 h⟩

/-- **Level 43/3** is realized by exactly four labellings: `3`/`3̄` on the short arm,
its conjugate on one long arm, the octet on the other. -/
theorem theta_level_43_3_iff (a b c : Irrep) :
    (admissible a b c = true ∧ level3 a b c = 43) ↔ (a, b, c) ∈ level43List := by
  constructor
  · intro ⟨ha, hl⟩
    have hm := (theta_enumeration a b c).1 ⟨ha, by omega⟩
    exact (level43_char _ hm).1 hl
  · intro h
    have hm := level43List_sub _ h
    exact ⟨((theta_enumeration a b c).2 hm).1, (level43_char _ hm).2 h⟩

theorem level40List_length : level40List.length = 4 := by decide
theorem level43List_length : level43List.length = 4 := by decide

theorem levels_of_list : ∀ t ∈ thetaList, level3 t.1 t.2.1 t.2.2 ∈ levelSet3 := by decide
theorem levels_realized : ∀ n ∈ levelSet3, ∃ t ∈ thetaList, level3 t.1 t.2.1 t.2.2 = n := by
  decide

/-- **Full level set.** For `n ≤ 51`, `n/3` is the level of some admissible labelling iff
`n` is one of 16, 24, 28, 33, 34, 36, 40, 43, 46, 49, 51 (listed in increasing order). -/
theorem theta_levels (n : Nat) (hn : n ≤ 51) :
    (∃ a b c : Irrep, admissible a b c = true ∧ level3 a b c = n) ↔ n ∈ levelSet3 := by
  constructor
  · intro ⟨a, b, c, ha, hl⟩
    have hm := (theta_enumeration a b c).1 ⟨ha, by omega⟩
    have := levels_of_list _ hm
    simpa [hl] using this
  · intro h
    obtain ⟨⟨a, b, c⟩, hm, hl⟩ := levels_realized n h
    exact ⟨a, b, c, ((theta_enumeration a b c).2 hm).1, hl⟩

theorem levelSet3_sorted : levelSet3.Pairwise (· < ·) := by decide

/-- Lowest admissible level is 16/3; nothing nontrivial below it. -/
theorem theta_floor (a b c : Irrep) (h : admissible a b c = true) : 16 ≤ level3 a b c := by
  by_cases hl : level3 a b c ≤ 51
  · have hm := (theta_enumeration a b c).1 ⟨h, hl⟩
    have := levels_of_list _ hm
    have key : ∀ n ∈ levelSet3, 16 ≤ n := by decide
    exact key _ this
  · omega

end ThetaFloor
