import Mathlib.Data.Real.Basic
import KyFanChord

/- False control: drops the factor 2 on the E₀ upper bound. Must fail to compile.
   Counterexample: E₀ = 1, E₁ = 1, u = 1, sa = sb = 2 gives 1 ≤ 0. -/
namespace KyFanChord

theorem chord_gap_lower_no_two (E₀ E₁ u : ℝ → ℝ) {a b sa sb t : ℝ} (hab : a ≤ b)
    (hconc : ConcaveOn ℝ (Set.Icc a b) (fun κ => E₀ κ + E₁ κ))
    (ha : sa ≤ E₀ a + E₁ a) (hb : sb ≤ E₀ b + E₁ b)
    (hu : ∀ κ ∈ Set.Icc a b, E₀ κ ≤ u κ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * sa + t * sb - u ((1 - t) * a + t * b)
      ≤ E₁ ((1 - t) * a + t * b) - E₀ ((1 - t) * a + t * b) := by
  have hmem : (1 - t) * a + t * b ∈ Set.Icc a b := by constructor <;> nlinarith
  have hc := hconc.2 (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab)
    (by linarith : (0:ℝ) ≤ 1 - t) ht0 (by ring : (1 - t) + t = 1)
  simp only [smul_eq_mul] at hc
  have h1 := hu _ hmem
  nlinarith

end KyFanChord
