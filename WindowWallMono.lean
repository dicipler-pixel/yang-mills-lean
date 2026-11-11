import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Slope
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
  Monotonicity in the coupling ("and above").
  With g(κ, λ) = κ · e(λ/κ) and e concave on [0, ∞), the λ-increment
  g(κ, l₂) − g(κ, l₁) is nondecreasing in κ; equivalently the κ-forward secant
  g(c+h, λ) − g(c, λ) is nondecreasing in λ.  So a certified exclusion at one
  coupling holds at every larger coupling (same graph, even split, α = 1).
  Concavity of e (a minimum of lines in t) is a hypothesis.
-/

namespace WindowWallMono

open Set

/-- Secants of a concave function decrease when both endpoints move right. -/
theorem secant_anti {e : ℝ → ℝ} {S : Set ℝ} (he : ConcaveOn ℝ S e)
    {a₁ b₁ a₂ b₂ : ℝ} (ha₁ : a₁ ∈ S) (hb₁ : b₁ ∈ S) (ha₂ : a₂ ∈ S) (hb₂ : b₂ ∈ S)
    (h₂ : a₂ < b₂) (h₁ : a₁ < b₁) (ha : a₂ ≤ a₁) (hb : b₂ ≤ b₁) :
    (e b₁ - e a₁) / (b₁ - a₁) ≤ (e b₂ - e a₂) / (b₂ - a₂) := by
  have cv : ConvexOn ℝ S (fun t => -e t) := he.neg
  have conc : ∀ {a x y : ℝ}, a ∈ S → x ∈ S → y ∈ S → x ≠ a → y ≠ a → x ≤ y →
      (e y - e a) / (y - a) ≤ (e x - e a) / (x - a) := by
    intro a x y ha hx hy hxa hya hxy
    have := cv.secant_mono ha hx hy hxa hya hxy
    have q : ∀ u v : ℝ, (-e u - -e v) / (u - v) = -((e u - e v) / (u - v)) := by
      intro u v; rw [← neg_div]; ring_nf
    rw [q, q] at this
    linarith
  -- anchor at a₂: moving the right end from b₂ to b₁ lowers the slope
  have s1 : (e b₁ - e a₂) / (b₁ - a₂) ≤ (e b₂ - e a₂) / (b₂ - a₂) :=
    conc ha₂ hb₂ hb₁ h₂.ne' (by linarith : b₁ ≠ a₂) hb
  -- anchor at b₁: moving the left end from a₂ to a₁ lowers the slope
  have s2 : (e b₁ - e a₁) / (b₁ - a₁) ≤ (e b₁ - e a₂) / (b₁ - a₂) := by
    have := conc hb₁ ha₂ ha₁ (by linarith : a₂ ≠ b₁) h₁.ne ha
    have r : ∀ u v : ℝ, (e v - e u) / (v - u) = (e u - e v) / (u - v) := by
      intro u v; rw [← neg_sub (e u), ← neg_sub u, neg_div_neg_eq]
    rwa [r b₁ a₁, r b₁ a₂] at this
  exact s2.trans s1

/-- The λ-increment of g(κ, λ) = κ e(λ/κ) is nondecreasing in κ. -/
theorem increment_mono {e : ℝ → ℝ} (he : ConcaveOn ℝ (Ici 0) e)
    {κ₁ κ₂ l₁ l₂ : ℝ} (hκ₁ : 0 < κ₁) (hκ : κ₁ ≤ κ₂) (hl₁ : 0 ≤ l₁) (hl : l₁ < l₂) :
    κ₁ * e (l₂ / κ₁) - κ₁ * e (l₁ / κ₁) ≤ κ₂ * e (l₂ / κ₂) - κ₂ * e (l₁ / κ₂) := by
  have hκ₂ : 0 < κ₂ := lt_of_lt_of_le hκ₁ hκ
  have mem : ∀ {t κ : ℝ}, 0 ≤ t → 0 < κ → t / κ ∈ Ici (0:ℝ) :=
    fun ht hk => mem_Ici.mpr (div_nonneg ht hk.le)
  have hl₂ : 0 ≤ l₂ := by linarith
  have l1 : l₁ / κ₁ < l₂ / κ₁ := div_lt_div_of_pos_right hl hκ₁
  have l2 : l₁ / κ₂ < l₂ / κ₂ := div_lt_div_of_pos_right hl hκ₂
  have key := secant_anti he (mem hl₁ hκ₁) (mem hl₂ hκ₁) (mem hl₁ hκ₂) (mem hl₂ hκ₂) l2 l1
    (div_le_div_of_nonneg_left hl₁ hκ₁ hκ) (div_le_div_of_nonneg_left hl₂ hκ₁ hκ)
  have d1 : l₂ / κ₁ - l₁ / κ₁ = (l₂ - l₁) / κ₁ := by ring
  have d2 : l₂ / κ₂ - l₁ / κ₂ = (l₂ - l₁) / κ₂ := by ring
  have hd : 0 < l₂ - l₁ := sub_pos.mpr hl
  rw [d1, d2, div_div_eq_mul_div, div_div_eq_mul_div,
    div_le_div_iff₀ hd hd] at key
  have := mul_le_mul_of_nonneg_right key hd.le
  nlinarith [mul_pos hd hd]

/-- Equivalent form: the κ-forward secant is nondecreasing in λ. -/
theorem forward_secant_mono {e : ℝ → ℝ} (he : ConcaveOn ℝ (Ici 0) e)
    {c h l₁ l₂ : ℝ} (hc : 0 < c) (hh : 0 ≤ h) (hl₁ : 0 ≤ l₁) (hl : l₁ < l₂) :
    (c + h) * e (l₁ / (c + h)) - c * e (l₁ / c)
      ≤ (c + h) * e (l₂ / (c + h)) - c * e (l₂ / c) := by
  have := increment_mono he hc (by linarith : c ≤ c + h) hl₁ hl
  linarith

/-- False control: for a strictly convex e the increment shrinks with κ. -/
theorem control_needs_concavity :
    ∃ e : ℝ → ℝ, ¬ (1 * e (2 / 1) - 1 * e (1 / 1) ≤ 2 * e (2 / 2) - 2 * e (1 / 2)) := by
  refine ⟨fun t => t * t, ?_⟩
  norm_num

end WindowWallMono

#print axioms WindowWallMono.increment_mono
#print axioms WindowWallMono.forward_secant_mono
#print axioms WindowWallMono.control_needs_concavity
