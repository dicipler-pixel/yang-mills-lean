import Mathlib

/-!
# Finite retained/hidden coupling and feedback kernels

This module formalizes only finite real-matrix statements used by the current
Yang--Mills truncation.  It does not identify a full continuum memory kernel or
claim a mass gap.
-/

open Matrix

namespace YangMillsFinite

variable {r h : Type*} [Fintype r] [Fintype h]

/-- Symmetric retained/hidden redistribution block. -/
def redistribution (B : Matrix r h ℝ) : Matrix (Sum r h) (Sum r h) ℝ :=
  Matrix.fromBlocks 0 B B.transpose 0

/-- Zero-time retained feedback Gram. -/
def memoryAtZero (B : Matrix r h ℝ) : Matrix r r ℝ :=
  B * B.transpose

/-- Redistribution vanishes exactly when the coupling block vanishes. -/
theorem redistribution_eq_zero_iff (B : Matrix r h ℝ) :
    redistribution B = 0 ↔ B = 0 := by
  constructor
  · intro hB
    ext i j
    have h := congrArg (fun M : Matrix (Sum r h) (Sum r h) ℝ =>
      M (Sum.inl i) (Sum.inr j)) hB
    simpa [redistribution] using h
  · intro hB
    subst B
    simp [redistribution]

/-- The zero-time feedback Gram vanishes exactly when the coupling block does. -/
theorem memoryAtZero_eq_zero_iff (B : Matrix r h ℝ) :
    memoryAtZero B = 0 ↔ B = 0 := by
  constructor
  · intro hK
    ext i j
    have hdiag := congrArg (fun M : Matrix r r ℝ => M i i) hK
    have hsum : (∑ k, (B i k)^2) = 0 := by
      simpa [memoryAtZero, Matrix.mul_apply, Matrix.transpose_apply, pow_two] using hdiag
    have hle : (B i j)^2 ≤ ∑ k, (B i k)^2 := by
      exact Finset.single_le_sum
        (fun k hk => sq_nonneg (B i k))
        (Finset.mem_univ j)
    rw [hsum] at hle
    have hsquare : (B i j)^2 = 0 :=
      le_antisymm hle (sq_nonneg (B i j))
    simpa using (sq_eq_zero_iff.mp hsquare)
  · intro hB
    subst B
    simp [memoryAtZero]

/-- Retained feedback associated with a hidden response matrix. -/
def feedbackWith (B : Matrix r h ℝ) (R : Matrix h h ℝ) : Matrix r r ℝ :=
  B * R * B.transpose

/-- A Gram-factorized response is the zero-time Gram of the transformed coupling. -/
theorem feedbackWith_factorized
    (B : Matrix r h ℝ) (R C : Matrix h h ℝ)
    (hR : R = C * C.transpose) :
    feedbackWith B R = memoryAtZero (B * C) := by
  rw [feedbackWith, hR, memoryAtZero, Matrix.transpose_mul]
  simp [Matrix.mul_assoc]

/-- If the factor has an explicit right inverse, zero feedback is equivalent to zero coupling. -/
theorem feedbackWith_eq_zero_iff_of_factor_right_inverse
    [DecidableEq h]
    (B : Matrix r h ℝ) (R C L : Matrix h h ℝ)
    (hR : R = C * C.transpose)
    (hCL : C * L = 1) :
    feedbackWith B R = 0 ↔ B = 0 := by
  constructor
  · intro hfb
    have hgram : memoryAtZero (B * C) = 0 := by
      rw [← feedbackWith_factorized B R C hR]
      exact hfb
    have hBC : B * C = 0 := (memoryAtZero_eq_zero_iff (B * C)).mp hgram
    calc
      B = B * (C * L) := by rw [hCL, Matrix.mul_one]
      _ = (B * C) * L := by rw [Matrix.mul_assoc]
      _ = 0 := by rw [hBC, Matrix.zero_mul]
  · intro hB
    subst B
    simp [feedbackWith]

section PositiveResponse

variable [DecidableEq r] [DecidableEq h]

/-- The diagonal of the retained feedback is the quadratic response of the
corresponding row of the coupling matrix. -/
theorem feedbackWith_diag
    (B : Matrix r h ℝ) (R : Matrix h h ℝ) (i : r) :
    feedbackWith B R i i = (B i) ⬝ᵥ (R *ᵥ B i) := by
  simp only [feedbackWith, Matrix.mul_apply, Matrix.transpose_apply,
    dotProduct, Matrix.mulVec]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp [mul_assoc]

/-- A positive-definite hidden response detects every nonzero retained-hidden
coupling through the full feedback matrix. -/
theorem feedbackWith_eq_zero_iff_of_posDef
    (B : Matrix r h ℝ) (R : Matrix h h ℝ)
    (hR : R.PosDef) :
    feedbackWith B R = 0 ↔ B = 0 := by
  constructor
  · intro hfeedback
    ext i j
    have hdiag : (feedbackWith B R) i i = 0 := by
      simpa using congr_fun (congr_fun hfeedback i) i
    have hquad : (B i) ⬝ᵥ (R *ᵥ B i) = 0 := by
      rw [← feedbackWith_diag B R i]
      exact hdiag
    by_contra hij
    have hrow : B i ≠ 0 := by
      intro hzero
      exact hij (congr_fun hzero j)
    have hpos : 0 < (B i) ⬝ᵥ (R *ᵥ B i) := by
      simpa using hR.dotProduct_mulVec_pos hrow
    exact (ne_of_gt hpos) hquad
  · intro hB
    subst B
    simp [feedbackWith]

/-- A nonzero retained-hidden coupling has nonzero feedback against every
positive-definite finite hidden response. -/
theorem nonzero_coupling_gives_nonzero_posDef_feedback
    (B : Matrix r h ℝ) (R : Matrix h h ℝ)
    (hR : R.PosDef) (hB : B ≠ 0) :
    feedbackWith B R ≠ 0 := by
  intro hzero
  exact hB ((feedbackWith_eq_zero_iff_of_posDef B R hR).mp hzero)

end PositiveResponse

end YangMillsFinite

#print axioms YangMillsFinite.redistribution_eq_zero_iff
#print axioms YangMillsFinite.memoryAtZero_eq_zero_iff
#print axioms YangMillsFinite.feedbackWith_factorized
#print axioms YangMillsFinite.feedbackWith_eq_zero_iff_of_factor_right_inverse
#print axioms YangMillsFinite.feedbackWith_diag
#print axioms YangMillsFinite.feedbackWith_eq_zero_iff_of_posDef
#print axioms YangMillsFinite.nonzero_coupling_gives_nonzero_posDef_feedback
