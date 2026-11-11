import Mathlib.Analysis.SpecialFunctions.Log.Basic

/- False control: claims the decay rate is twice the gap. Must fail to compile. -/
namespace TransferGap

theorem decay_rate_double (a E₀ E₁ : ℝ) :
    -Real.log (Real.exp (-(a * E₁)) / Real.exp (-(a * E₀))) = 2 * a * (E₁ - E₀) := by
  rw [← Real.exp_sub, Real.log_exp]
  ring

end TransferGap
