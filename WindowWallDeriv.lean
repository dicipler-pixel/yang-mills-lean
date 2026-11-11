import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
  Round five window wall: the concavity / secant step.

  * `slope_far_le_near`: for concave g and x < y < z, the long secant is below the short one.
  * `secant_le_deriv`: for concave g, g'(κ) ≥ (g(κ+h) − g(κ))/h for h > 0.
  * `certified_secant_le_deriv`: the same with certified endpoints g_lo(κ+h) ≤ g(κ+h), g(κ) ≤ g_hi(κ).
  * `wall_nonpos` / `no_window`: W concave, W 0 = 0, W'(0) ≤ 0 ⇒ W s ≤ 0 for s ≥ 0,
    so d − r ≤ W s gives d − r ≤ 0 (no positive window in that allocation class).
  Analytic inputs (concavity of the ground energy, existence of g') are hypotheses.
-/

namespace WindowWallDeriv

open Filter Topology Set

theorem slope_far_le_near {g : ℝ → ℝ} (hg : ConcaveOn ℝ univ g) {x y z : ℝ}
    (hxy : x < y) (hyz : y < z) :
    (g z - g x) / (z - x) ≤ (g y - g x) / (y - x) := by
  have hadj := hg.slope_anti_adjacent (mem_univ x) (mem_univ z) hxy hyz
  have h1 : 0 < y - x := sub_pos.mpr hxy
  have h2 : 0 < z - y := sub_pos.mpr hyz
  have h3 : 0 < z - x := by linarith
  rw [div_le_div_iff₀ h2 h1] at hadj
  rw [div_le_div_iff₀ h3 h1]
  nlinarith

theorem secant_le_deriv {g : ℝ → ℝ} (hg : ConcaveOn ℝ univ g) {κ d h : ℝ}
    (hd : HasDerivAt g d κ) (hh : 0 < h) :
    (g (κ + h) - g κ) / h ≤ d := by
  have ht := hd.tendsto_slope_zero_right
  apply ge_of_tendsto ht
  have hmem : Ioo (0:ℝ) h ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT hh
  filter_upwards [hmem] with t ht
  obtain ⟨ht0, hth⟩ := ht
  have := slope_far_le_near hg (x := κ) (y := κ + t) (z := κ + h) (by linarith) (by linarith)
  simp only [add_sub_cancel_left] at this
  rw [smul_eq_mul, inv_mul_eq_div]
  exact this

theorem certified_secant_le_deriv {g gLo gHi : ℝ → ℝ} (hg : ConcaveOn ℝ univ g) {κ d h : ℝ}
    (hd : HasDerivAt g d κ) (hh : 0 < h)
    (hlo : gLo (κ + h) ≤ g (κ + h)) (hhi : g κ ≤ gHi κ) :
    (gLo (κ + h) - gHi κ) / h ≤ d := by
  have := secant_le_deriv hg hd hh
  have hnum : gLo (κ + h) - gHi κ ≤ g (κ + h) - g κ := by linarith
  exact (div_le_div_of_nonneg_right hnum hh.le).trans this

theorem wall_nonpos {W : ℝ → ℝ} (hW : ConcaveOn ℝ univ W) (h0 : W 0 = 0) {w0 : ℝ}
    (hd : HasDerivAt W w0 0) (hslope : w0 ≤ 0) {s : ℝ} (hs : 0 ≤ s) : W s ≤ 0 := by
  rcases hs.eq_or_lt with rfl | hs
  · simp [h0]
  have := secant_le_deriv hW hd hs
  simp only [zero_add, h0, sub_zero] at this
  have : W s ≤ w0 * s := (div_le_iff₀ hs).mp this
  nlinarith

theorem no_window {W : ℝ → ℝ} (hW : ConcaveOn ℝ univ W) (h0 : W 0 = 0) {w0 : ℝ}
    (hd : HasDerivAt W w0 0) (hslope : w0 ≤ 0) {s d r : ℝ} (hs : 0 ≤ s)
    (hwin : d - r ≤ W s) : d - r ≤ 0 :=
  hwin.trans (wall_nonpos hW h0 hd hslope hs)

/-- False control: without concavity the wall fails (W s = s·s, W'(0) = 0, W 1 = 1 > 0). -/
theorem control_needs_concavity :
    ∃ W : ℝ → ℝ, W 0 = 0 ∧ HasDerivAt W 0 0 ∧ 0 < W 1 := by
  refine ⟨fun s => s * s, by simp, ?_, by norm_num⟩
  have h := (hasDerivAt_id' (0:ℝ)).mul (hasDerivAt_id' (0:ℝ))
  have e : (1:ℝ) * 0 + 0 * 1 = 0 := by norm_num
  rw [e] at h
  exact h

end WindowWallDeriv

#print axioms WindowWallDeriv.certified_secant_le_deriv
#print axioms WindowWallDeriv.no_window
#print axioms WindowWallDeriv.control_needs_concavity
