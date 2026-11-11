import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# TransferGap: the transfer-matrix decay rate is an algebraic identity

For real `a`, `E₀`, `E₁`, put `t₀ = exp(−a·E₀)` and `t₁ = exp(−a·E₁)`. Then
`−log(t₁ / t₀) = a·(E₁ − E₀)` exactly.

This is an algebraic identity, nothing more. If the transfer-matrix eigenvalues are
computed as `exp(−a·E)` from the spectrum of the Hamiltonian `H`, then the decay rate
`−log(t₁/t₀)` returns exactly `a` times the gap of `H` that was put in. The transfer-matrix
decay rate computed from `H` is therefore NOT independent evidence for the mass gap;
it restates the `H` gap.
-/

namespace TransferGap

/-- `−log(t₁/t₀) = a·(E₁ − E₀)` for `t₀ = exp(−a·E₀)`, `t₁ = exp(−a·E₁)`. -/
theorem decay_rate_eq_gap (a E₀ E₁ : ℝ) :
    -Real.log (Real.exp (-(a * E₁)) / Real.exp (-(a * E₀))) = a * (E₁ - E₀) := by
  rw [← Real.exp_sub, Real.log_exp]
  ring

/-- Same identity with `t₀, t₁` named. -/
theorem decay_rate_eq_gap' (a E₀ E₁ t₀ t₁ : ℝ) (h₀ : t₀ = Real.exp (-(a * E₀)))
    (h₁ : t₁ = Real.exp (-(a * E₁))) : -Real.log (t₁ / t₀) = a * (E₁ - E₀) := by
  subst h₀ h₁
  exact decay_rate_eq_gap a E₀ E₁

end TransferGap

