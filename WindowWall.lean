/-
Window wall, derivative-free and certifiable (round five).
`W` is the window bound on the allocation class: `d - r ≤ W s`, `W 0 = 0`, `W` concave on `s ≥ 0`.
Everything here uses finite secants only, so certified energy endpoints are enough;
no derivative of a floating-point ground state is needed.
-/
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Set

namespace WindowWall

/-- If one certified secant from `0` is nonpositive, the window is closed from that step on. -/
theorem wall_of_secant {W : ℝ → ℝ} (hW : ConcaveOn ℝ (Ici 0) W) (h0 : W 0 = 0)
    {h : ℝ} (hh : 0 < h) (hWh : W h ≤ 0) {t : ℝ} (ht : h ≤ t) : W t ≤ 0 := by
  rcases eq_or_lt_of_le ht with rfl | hlt
  · exact hWh
  have key := hW.slope_anti_adjacent (x := 0) (y := h) (z := t)
    (by simp) (by simp; linarith) hh hlt
  rw [h0, sub_zero, sub_zero] at key
  have hs : W h / h ≤ 0 := div_nonpos_of_nonpos_of_nonneg hWh hh.le
  have : (W t - W h) / (t - h) ≤ 0 := key.trans hs
  have htpos : 0 < t - h := by linarith
  have : W t - W h ≤ 0 := by
    have := mul_le_mul_of_nonneg_right this htpos.le
    rwa [div_mul_cancel₀ _ htpos.ne', zero_mul] at this
  linarith

/-- Stronger form: on `t ≥ h` the bound lies below the secant line, `W t ≤ (t / h) W h`. -/
theorem le_secant_line {W : ℝ → ℝ} (hW : ConcaveOn ℝ (Ici 0) W) (h0 : W 0 = 0)
    {h t : ℝ} (hh : 0 < h) (ht : h < t) : W t ≤ t / h * W h := by
  have key := hW.slope_anti_adjacent (x := 0) (y := h) (z := t)
    (by simp) (by simp; linarith) hh ht
  rw [h0, sub_zero, sub_zero] at key
  have htpos : 0 < t - h := by linarith
  rw [div_le_div_iff₀ htpos hh] at key
  rw [div_mul_eq_mul_div, le_div_iff₀ hh]
  nlinarith [key]

/-- The certified wall: an upper energy bound `Wbar ≥ W h` with `Wbar ≤ 0` closes the window
for every `t ≥ h`. -/
theorem wall_certified {W : ℝ → ℝ} (hW : ConcaveOn ℝ (Ici 0) W) (h0 : W 0 = 0)
    {h Wbar : ℝ} (hh : 0 < h) (hup : W h ≤ Wbar) (hneg : Wbar ≤ 0) {t : ℝ} (ht : h ≤ t) :
    W t ≤ 0 :=
  wall_of_secant hW h0 hh (hup.trans hneg) ht

/-- Certified secant comparison for a concave energy `g` (the derivative-free form of
`g'(κ) ≥ (g_lo(κ+h) - g_hi(κ)) / h`): with `a < b < c` and endpoint bounds
`g_lo c ≤ g c`, `g b ≤ g_hi b`, the certified forward secant is below the backward secant. -/
theorem certified_secant {g : ℝ → ℝ} {S : Set ℝ} (hg : ConcaveOn ℝ S g)
    {a b c glo ghi : ℝ} (ha : a ∈ S) (hc : c ∈ S) (hab : a < b) (hbc : b < c)
    (hlo : glo ≤ g c) (hhi : g b ≤ ghi) :
    (glo - ghi) / (c - b) ≤ (g b - g a) / (b - a) := by
  have key := hg.slope_anti_adjacent ha hc hab hbc
  have hcb : 0 < c - b := by linarith
  have : (glo - ghi) / (c - b) ≤ (g c - g b) / (c - b) :=
    div_le_div_of_nonneg_right (by linarith) hcb.le
  exact this.trans key

/-- False control: without concavity the wall fails. `W s = s² - s` has `W 0 = 0`, `W 1 ≤ 0`,
yet `W 2 > 0`. -/
theorem wall_needs_concavity :
    ¬ ∀ W : ℝ → ℝ, W 0 = 0 → W 1 ≤ 0 → W 2 ≤ 0 := by
  intro H
  have := H (fun s => s ^ 2 - s) (by norm_num) (by norm_num)
  norm_num at this

end WindowWall
