import ThetaFloor

/-!
# ThetaTriality: triality conservation for the SU(3) singlet rule (core Lean)

`triality (p, q) = (p + 2q) % 3`, so `3 = (1,0)` has triality 1, `3̄ = (0,1)` has 2 and
`8 = (1,1)` has 0. Since `S₁ + S₂ = 3(Σp + Σq)` with `S₂ = Σp + 2Σq ≡ Σ triality`,
the `3 ∣ S₁` clause of `ThetaFloor.hasSinglet` forces total triality 0. The singlet rule
itself is the closed formula of `ThetaFloor` (cross-checked numerically there, not
derived from representation theory in Lean); everything here is proved for all labels,
with no bound on `p, q`.
-/

namespace ThetaTriality

open ThetaFloor

/-- SU(3) triality (N-ality) of the irrep with Dynkin labels `(p, q)`. -/
def triality (x : Irrep) : Nat := (x.1 + 2 * x.2) % 3

/-- The conjugate irrep `(p, q) ↦ (q, p)`. -/
def conj (x : Irrep) : Irrep := (x.2, x.1)

theorem triality_fund : triality (1, 0) = 1 := by decide
theorem triality_antifund : triality (0, 1) = 2 := by decide
theorem triality_adjoint : triality (1, 1) = 0 := by decide

/-- Conjugation negates triality mod 3. -/
theorem triality_conj (x : Irrep) : (triality x + triality (conj x)) % 3 = 0 := by
  obtain ⟨p, q⟩ := x
  simp only [triality, conj]
  omega

/-- The singlet rule conserves triality (general, all labels). -/
theorem singlet_triality (a b c : Irrep) (h : hasSinglet a b c = true) :
    (triality a + triality b + triality c) % 3 = 0 := by
  obtain ⟨p1, q1⟩ := a
  obtain ⟨p2, q2⟩ := b
  obtain ⟨p3, q3⟩ := c
  simp only [hasSinglet, Bool.and_eq_true, beq_iff_eq] at h
  simp only [triality]
  omega

/-- Theta corollary: at both vertices of an admissible labelling the total triality is 0
(the first vertex sees `a, b, c`, the second their conjugates). -/
theorem theta_vertex_triality (a b c : Irrep) (h : admissible a b c = true) :
    (triality a + triality b + triality c) % 3 = 0 ∧
    (triality (conj a) + triality (conj b) + triality (conj c)) % 3 = 0 := by
  have hs : hasSinglet a b c = true := by
    simp only [admissible, Bool.and_eq_true] at h
    exact h.1
  have h1 := singlet_triality a b c hs
  have ha := triality_conj a
  have hb := triality_conj b
  have hc := triality_conj c
  exact ⟨h1, by omega⟩

/-- No lone triality: an admissible labelling never has exactly one arm of nonzero
triality (a link carrying triality cannot end). -/
theorem no_lone_triality (a b c : Irrep) (h : admissible a b c = true) :
    ¬ ((triality a ≠ 0 ∧ triality b = 0 ∧ triality c = 0) ∨
       (triality a = 0 ∧ triality b ≠ 0 ∧ triality c = 0) ∨
       (triality a = 0 ∧ triality b = 0 ∧ triality c ≠ 0)) := by
  have h1 := (theta_vertex_triality a b c h).1
  have ha : triality a < 3 := Nat.mod_lt _ (by decide)
  have hb : triality b < 3 := Nat.mod_lt _ (by decide)
  have hc : triality c < 3 := Nat.mod_lt _ (by decide)
  omega

/-- Stronger, also general: no admissible labelling has exactly one non-trivial arm
(this covers triality-0 irreps such as the octet as well). -/
theorem no_lone_arm (x : Irrep) (hx : x ≠ (0, 0)) :
    hasSinglet x (0, 0) (0, 0) = false ∧ hasSinglet (0, 0) x (0, 0) = false ∧
    hasSinglet (0, 0) (0, 0) x = false := by
  obtain ⟨p, q⟩ := x
  have hpq : p + q ≠ 0 := by
    intro h0
    apply hx
    have hp : p = 0 := by omega
    have hq : q = 0 := by omega
    rw [hp, hq]
  refine ⟨?_, ?_, ?_⟩ <;>
  · apply Bool.eq_false_iff.mpr
    intro h
    simp only [hasSinglet, Bool.and_eq_true, Nat.ble_eq] at h
    simp only [Nat.min_def] at h
    split at h <;> omega

end ThetaTriality
