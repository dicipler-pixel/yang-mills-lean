import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
  One-link SU(3) tail floor.

  For the irrep (p, q), three times the quadratic Casimir is
      3·C₂(p, q) = p² + q² + pq + 3p + 3q.
  `su3_character_certificate.py` truncates at total p + q ≤ n and uses the tail floor
      tail_floor(n) = (s² − ⌊s²/4⌋ + 3s)/3,  s = n + 1,
  as a lower bound for C₂ on every omitted state. This file proves that bound for all
  shells p + q ≥ n + 1, and that it is attained on the first omitted shell, so it is the
  exact minimum there.

  Scope: this is a single-link (one-loop) statement. It is NOT the graph floor 28/3, which
  is a bound on total Casimir over gauge-invariant states and needs SU(3) tensor rules plus
  graph combinatorics (see `cross_theorem/proofs/SPATIAL_BASES.md`).

  Frozen statements (do not edit without review):
    `tail_floor_le`      : n + 1 ≤ p + q → T(n) ≤ 3·C₂(p, q)
    `tail_floor_attained`: 3·C₂(s/2, s − s/2) = T(n) with s = n + 1
  where T(n) = s·s − s·s/4 + 3·s (natural-number division).
-/

namespace OneLinkTailFloor

/-- Three times the SU(3) quadratic Casimir of the irrep (p, q). -/
def casimir3 (p q : ℕ) : ℕ := p * p + q * q + p * q + 3 * p + 3 * q

/-- Three times the repo's one-loop tail floor at truncation n (s = n + 1). -/
def tailFloor3 (n : ℕ) : ℕ := (n + 1) * (n + 1) - (n + 1) * (n + 1) / 4 + 3 * (n + 1)

private lemma four_mul_le (p q : ℕ) : 4 * (p * q) ≤ (p + q) * (p + q) := by
  have : (0 : ℤ) ≤ ((p : ℤ) - q) * ((p : ℤ) - q) := mul_self_nonneg _
  have h : (4 * (p * q) : ℤ) ≤ ((p + q) * (p + q) : ℤ) := by nlinarith
  exact_mod_cast h

/-- Frozen statement 1: the tail floor is a lower bound on every omitted irrep. -/
theorem tail_floor_le {n p q : ℕ} (h : n + 1 ≤ p + q) :
    tailFloor3 n ≤ casimir3 p q := by
  unfold tailFloor3 casimir3
  have hA : (p + q) * (p + q) = p * p + q * q + 2 * (p * q) := by ring
  have hB := four_mul_le p q
  have hT : (n + 1) * (n + 1) ≤ (p + q) * (p + q) := Nat.mul_le_mul h h
  generalize (n + 1) * (n + 1) = X at hT ⊢
  generalize (p + q) * (p + q) = A at hA hB hT
  generalize p * q = B at hA hB ⊢
  generalize p * p + q * q = C at hA ⊢
  omega

/-- Frozen statement 2: the floor is attained on the first omitted shell. -/
theorem tail_floor_attained (n : ℕ) :
    casimir3 ((n + 1) / 2) ((n + 1) - (n + 1) / 2) = tailFloor3 n := by
  unfold casimir3 tailFloor3
  rcases Nat.even_or_odd' (n + 1) with ⟨k, hk | hk⟩
  · rw [hk]
    have h1 : 2 * k / 2 = k := by omega
    have h2 : 2 * k - k = k := by omega
    have h4 : 2 * k * (2 * k) = 4 * (k * k) := by ring
    have h3 : 4 * (k * k) / 4 = k * k := by omega
    rw [h1, h2, h4, h3]
    generalize k * k = K
    omega
  · rw [hk]
    have h1 : (2 * k + 1) / 2 = k := by omega
    have h2 : 2 * k + 1 - k = k + 1 := by omega
    have h4 : (2 * k + 1) * (2 * k + 1) = 4 * (k * k + k) + 1 := by ring
    have h3 : (4 * (k * k + k) + 1) / 4 = k * k + k := by omega
    rw [h1, h2, h4, h3]
    have h5 : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
    have h6 : k * (k + 1) = k * k + k := by ring
    rw [h5, h6]
    generalize k * k = K
    omega

/-- False control: the floor is NOT a bound below the cutoff. At n = 1 the trivial irrep
    (0, 0), which is kept, has 3·C₂ = 0 < T(1) = 4 − 1 + 6 = 9. -/
theorem control_kept_state_below_floor : casimir3 0 0 < tailFloor3 1 := by decide

end OneLinkTailFloor

#print axioms OneLinkTailFloor.tail_floor_le
#print axioms OneLinkTailFloor.tail_floor_attained
#print axioms OneLinkTailFloor.control_kept_state_below_floor
