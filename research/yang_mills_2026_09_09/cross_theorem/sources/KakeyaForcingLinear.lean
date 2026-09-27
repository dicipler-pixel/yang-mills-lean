import Mathlib

/-! Exact algebraic forcing criteria. The projector theorem states its kernel,
fixing and symmetry hypotheses explicitly. No contour integral is assumed. -/
namespace OperatorFirst.KakeyaForcingLinear
open scoped RealInnerProductSpace

section Linear
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

def CanForce (A : V →ₗ[K] W) (b : V →ₗ[K] K) : Prop :=
  ∃ c, A c = 0 ∧ b c ≠ 0

theorem forcing_iff_kernel_not_le (A : V →ₗ[K] W) (b : V →ₗ[K] K) :
    CanForce A b ↔ ¬ LinearMap.ker A ≤ LinearMap.ker b := by
  classical
  constructor
  · rintro ⟨c, hc, hb⟩ hle
    exact hb (hle hc)
  · intro h
    by_contra hn
    apply h
    intro c hc
    change A c = 0 at hc
    change b c = 0
    by_contra hb
    exact hn ⟨c, hc, hb⟩

theorem dual_certificate (A : V →ₗ[K] W) (b : V →ₗ[K] K)
    (y : W →ₗ[K] K) (h : b = y.comp A) : ¬ CanForce A b := by
  rintro ⟨c, hc, hb⟩
  apply hb
  rw [h, LinearMap.comp_apply, hc, map_zero]

theorem presentation_invariant {U : Type*} [AddCommGroup U] [Module K U]
    (A : V →ₗ[K] W) (b : V →ₗ[K] K) (e : U ≃ₗ[K] V) :
    CanForce (A.comp e.toLinearMap) (b.comp e.toLinearMap) ↔ CanForce A b := by
  constructor
  · rintro ⟨c, hc, hb⟩
    exact ⟨e c, hc, hb⟩
  · rintro ⟨c, hc, hb⟩
    refine ⟨e.symm c, ?_, ?_⟩
    · simpa using hc
    · simpa using hb

theorem nonzero_target_rescaling (A : V →ₗ[K] W) (b : V →ₗ[K] K)
    (a : K) (ha : a ≠ 0) : CanForce A (a • b) ↔ CanForce A b := by
  simp only [CanForce, LinearMap.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero]
  simp [ha]

theorem shifted_operator_on_kernel (G : V →ₗ[K] V) (v : V)
    (hv : G v = 0) (z : K) (hz : z ≠ 0) :
    z • (z⁻¹ • v) - G (z⁻¹ • v) = v := by
  rw [map_smul, hv, smul_zero, sub_zero, smul_smul, mul_inv_cancel₀ hz, one_smul]

theorem inverse_on_kernel (G : V →ₗ[K] V) (R : V → V) (v : V)
    (hv : G v = 0) (z : K) (hz : z ≠ 0)
    (hR : ∀ x, R (z • x - G x) = x) : R v = z⁻¹ • v := by
  have h := hR (z⁻¹ • v)
  rwa [shifted_operator_on_kernel G v hv z hz] at h
end Linear

section Projection
variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [AddCommGroup W] [Module ℝ W]

theorem projector_detects_forcing (A : E →ₗ[ℝ] W) (P : E →ₗ[ℝ] E)
    (hAP : ∀ c, A (P c) = 0)
    (hfix : ∀ c, A c = 0 → P c = c)
    (hsym : ∀ x y, inner ℝ x (P y) = inner ℝ (P x) y) (v : E) :
    (∃ c, A c = 0 ∧ inner ℝ v c ≠ 0) ↔ 0 < inner ℝ v (P v) := by
  have hid : P (P v) = P v := hfix (P v) (hAP v)
  have heq : inner ℝ v (P v) = inner ℝ (P v) (P v) := by
    have h := hsym v (P v)
    rwa [hid] at h
  constructor
  · rintro ⟨c, hc, hn⟩
    have hp : P v ≠ 0 := by
      intro hz
      apply hn
      calc
        inner ℝ v c = inner ℝ v (P c) := by rw [hfix c hc]
        _ = inner ℝ (P v) c := hsym v c
        _ = 0 := by rw [hz]; simp
    rw [heq]
    exact lt_of_le_of_ne real_inner_self_nonneg (Ne.symm (inner_self_eq_zero.not.mpr hp))
  · intro h
    exact ⟨P v, hAP v, ne_of_gt h⟩
end Projection

theorem normalized_label_sum (a b : ℚ) (h : a+b ≠ 0) :
    a/(a+b) + b/(a+b) = 1 := by field_simp [h]

theorem normalized_difference (t s : ℚ) :
    (t-s, (1-t)-(1-s)) = (t-s, -(t-s)) := by congr 1 <;> ring

theorem normalized_difference_nonzero (t s : ℚ) (h : t ≠ s) : t-s ≠ 0 :=
  sub_ne_zero.mpr h

end OperatorFirst.KakeyaForcingLinear
#print axioms OperatorFirst.KakeyaForcingLinear.forcing_iff_kernel_not_le
#print axioms OperatorFirst.KakeyaForcingLinear.dual_certificate
#print axioms OperatorFirst.KakeyaForcingLinear.presentation_invariant
#print axioms OperatorFirst.KakeyaForcingLinear.nonzero_target_rescaling
#print axioms OperatorFirst.KakeyaForcingLinear.shifted_operator_on_kernel
#print axioms OperatorFirst.KakeyaForcingLinear.inverse_on_kernel
#print axioms OperatorFirst.KakeyaForcingLinear.projector_detects_forcing
#print axioms OperatorFirst.KakeyaForcingLinear.normalized_label_sum
#print axioms OperatorFirst.KakeyaForcingLinear.normalized_difference
#print axioms OperatorFirst.KakeyaForcingLinear.normalized_difference_nonzero
