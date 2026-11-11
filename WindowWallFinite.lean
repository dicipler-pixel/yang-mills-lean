import Mathlib.Analysis.Convex.Slope
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
  Round five window wall, derivative-free form (the main statement).

  For each plaquette p, with a rational step h_p > 0 and certified endpoints
  g_lo(c_p + h_p) ≤ g(c_p + h_p) and g(c_p) ≤ g_hi(c_p), put
  L_p = (g_lo(c_p + h_p) − g_hi(c_p)) / h_p.  For concave g on [0, ∞) and s ∈ (0, 1],
      W(s) = s·T − Σ_p [g_p(c_p) − g_p((1−s)c_p)] ≤ s·(T − Σ_p c_p L_p),
  so Σ_p c_p L_p ≥ T (T = 28/3) gives W(s) ≤ 0 for every s ∈ (0, 1]; at s = 0, W = 0.
  No derivatives, so level crossings need no special handling.

  Physics inputs taken as hypotheses: concavity of each ground energy in κ
  (minimum of affine functions), and d − r ≤ W(s) (LOCAL_ENERGY_FLOORS.md eqs. (1)–(2), α = 1,
  even allocation a_pe = (1−s)/r_e only).
-/

namespace WindowWallFinite

open Set

/-- Per plaquette: s·c·L ≤ g(c) − g((1−s)c) when L·h ≤ g(c+h) − g(c). -/
theorem plaquette_secant {g : ℝ → ℝ} (hg : ConcaveOn ℝ (Ici 0) g) {c h s L : ℝ}
    (hc : 0 < c) (hh : 0 < h) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hL : L * h ≤ g (c + h) - g c) :
    s * c * L ≤ g c - g ((1 - s) * c) := by
  have hx : (1 - s) * c ∈ Ici (0:ℝ) := mem_Ici.mpr (mul_nonneg (by linarith) hc.le)
  have hz : c + h ∈ Ici (0:ℝ) := mem_Ici.mpr (by linarith)
  have hxy : (1 - s) * c < c := by nlinarith
  have hyz : c < c + h := by linarith
  have hadj := hg.slope_anti_adjacent hx hz hxy hyz
  have e1 : c + h - c = h := by ring
  have e2 : c - (1 - s) * c = s * c := by ring
  rw [e1, e2] at hadj
  have hsc : 0 < s * c := mul_pos hs0 hc
  rw [div_le_div_iff₀ hh hsc] at hadj
  have h1 : L * h * (s * c) ≤ (g c - g ((1 - s) * c)) * h :=
    le_trans (mul_le_mul_of_nonneg_right hL hsc.le) hadj
  have h2 : s * c * L * h ≤ (g c - g ((1 - s) * c)) * h := by
    calc s * c * L * h = L * h * (s * c) := by ring
      _ ≤ _ := h1
  exact le_of_mul_le_mul_right h2 hh

/-- Certified endpoints give a valid L: L·h ≤ g(c+h) − g(c). -/
theorem certified_L {g gLo gHi : ℝ → ℝ} {c h : ℝ} (hh : 0 < h)
    (hlo : gLo (c + h) ≤ g (c + h)) (hhi : g c ≤ gHi c) :
    (gLo (c + h) - gHi c) / h * h ≤ g (c + h) - g c := by
  rw [div_mul_cancel₀ _ hh.ne']
  linarith

/-- The window bound: W(s) ≤ s·(T − Σ c_p L_p) for s ∈ (0, 1]. -/
theorem window_le {ι : Type*} (P : Finset ι) (g : ι → ℝ → ℝ)
    (hg : ∀ p ∈ P, ConcaveOn ℝ (Ici 0) (g p)) (c h L : ι → ℝ)
    (hc : ∀ p ∈ P, 0 < c p) (hh : ∀ p ∈ P, 0 < h p)
    (hL : ∀ p ∈ P, L p * h p ≤ g p (c p + h p) - g p (c p)) (T : ℝ) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s ≤ 1) :
    s * T - ∑ p ∈ P, (g p (c p) - g p ((1 - s) * c p)) ≤
      s * (T - ∑ p ∈ P, c p * L p) := by
  have hsum : ∑ p ∈ P, s * c p * L p ≤ ∑ p ∈ P, (g p (c p) - g p ((1 - s) * c p)) :=
    Finset.sum_le_sum fun p hp =>
      plaquette_secant (hg p hp) (hc p hp) (hh p hp) hs0 hs1 (hL p hp)
  have e : ∑ p ∈ P, s * c p * L p = s * ∑ p ∈ P, c p * L p := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [e] at hsum
  rw [mul_sub]
  linarith

/-- No window: if Σ c_p L_p ≥ T and d − r ≤ W(s) on (0, 1], then d − r ≤ 0 there. -/
theorem no_window {ι : Type*} (P : Finset ι) (g : ι → ℝ → ℝ)
    (hg : ∀ p ∈ P, ConcaveOn ℝ (Ici 0) (g p)) (c h L : ι → ℝ)
    (hc : ∀ p ∈ P, 0 < c p) (hh : ∀ p ∈ P, 0 < h p)
    (hL : ∀ p ∈ P, L p * h p ≤ g p (c p + h p) - g p (c p)) (T : ℝ)
    (hT : T ≤ ∑ p ∈ P, c p * L p) {d r s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hdr : d - r ≤ s * T - ∑ p ∈ P, (g p (c p) - g p ((1 - s) * c p))) :
    d - r ≤ 0 := by
  have hw := window_le P g hg c h L hc hh hL T hs0 hs1
  have : s * (T - ∑ p ∈ P, c p * L p) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hs0.le (by linarith)
  linarith

/-- False control: without concavity the per-plaquette step fails (g = x², c = h = 1, s = 1/2, L = 3). -/
theorem plaquette_needs_concavity :
    ¬ ((1:ℝ)/2 * 1 * 3 ≤ (1:ℝ)^2 - ((1 - 1/2) * 1)^2) := by norm_num

end WindowWallFinite
