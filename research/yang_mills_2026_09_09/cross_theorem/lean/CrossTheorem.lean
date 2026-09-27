import Mathlib

/- Finite/scalar closing steps of the cross-theorem gauge certificate.
   This does not formalize Peter-Weyl, Haar integration, Schur inertia, the
   infinite-dimensional local-window argument, or the45-state cube matrices. -/
namespace YangMillsCrossTheorem

 theorem denominator_positive (s c e offset z : ℝ)
    (hs : 0 ≤ s) (he : c ≤ e) (hz : z < s*c+offset) :
    0 < s*e+offset-z := by nlinarith

 theorem resolved_term_le (mass s c e offset z : ℝ)
    (hm : 0 ≤ mass) (hs : 0 ≤ s) (he : c ≤ e)
    (hz : z < s*c+offset) :
    mass/(s*e+offset-z) ≤ mass/(s*c+offset-z) := by
  apply div_le_div_of_nonneg_left hm
  · linarith
  · nlinarith

 theorem resolved_sum_le {ι : Type*} [Fintype ι]
    (mass energy : ι → ℝ) (s c offset z : ℝ)
    (hm : ∀ i, 0 ≤ mass i) (hs : 0 ≤ s) (he : ∀ i, c ≤ energy i)
    (hz : z < s*c+offset) :
    (∑ i, mass i/(s*energy i+offset-z)) ≤ (∑ i, mass i)/(s*c+offset-z) := by
  calc
    (∑ i, mass i/(s*energy i+offset-z)) ≤ ∑ i, mass i/(s*c+offset-z) := by
      apply Finset.sum_le_sum
      intro i _
      exact resolved_term_le (mass i) s c (energy i) offset z (hm i) hs (he i) hz
    _ = (∑ i, mass i)/(s*c+offset-z) := by rw [Finset.sum_div]

 theorem shared_shift_does_not_improve_floor (d r c : ℝ) :
    (d-c)-(r-c)=d-r := by ring

 theorem projection_margin (S : ℝ) (hS : S < 1) : 0 < 1-S := by linarith

 theorem window_error_nonnegative (omega S K : ℝ)
    (hw : 0 ≤ omega) (hS : 0 ≤ S) (hS1 : S < 1) (hK : 0 ≤ K) :
    0 ≤ (omega*S+K)/(1-S) := by
  exact div_nonneg (add_nonneg (mul_nonneg hw hS) hK) (le_of_lt (projection_margin S hS1))

 theorem budget_comparison (omega S K margin : ℝ) (hS : S < 1) :
    (omega*S+K)/(1-S) ≤ margin ↔ omega*S+K ≤ margin*(1-S) := by
  exact div_le_iff₀ (projection_margin S hS)

 theorem gap_transfer_closing_step (E0 E1 mu0 mu1 omega error : ℝ)
    (hground : E0 ≤ mu0)
    (hwindow : E1-E0 ≤ omega → mu1 ≤ E1+error) :
    min omega (mu1-mu0-error) ≤ E1-E0 := by
  by_cases h : E1-E0 ≤ omega
  · have hw := hwindow h
    exact le_trans (min_le_right _ _) (by linarith)
  · have hw : omega ≤ E1-E0 := by linarith
    exact le_trans (min_le_left _ _) hw

 theorem cube_local_allocation : (2 : ℚ)*(1-13/20)=7/10 := by norm_num

 theorem cube_allocated_floor :
    (13/20 : ℚ)*(28/3)+6*(92681/40000)=1198129/60000 := by norm_num

 theorem cube_endpoint_order :
    (8720479/500000 : ℚ) < 156407/8000 ∧
    (156407/8000 : ℚ) < 1198129/60000 := by norm_num

 theorem cube_margin :
    (156407/8000 : ℚ)-(8720479/500000)=2109917/1000000 := by norm_num

#print axioms denominator_positive
#print axioms resolved_term_le
#print axioms resolved_sum_le
#print axioms shared_shift_does_not_improve_floor
#print axioms projection_margin
#print axioms window_error_nonnegative
#print axioms budget_comparison
#print axioms gap_transfer_closing_step
#print axioms cube_local_allocation
#print axioms cube_allocated_floor
#print axioms cube_endpoint_order
#print axioms cube_margin
end YangMillsCrossTheorem
