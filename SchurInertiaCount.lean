import SchurInertiaComparison
import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-!
# One negative direction from a positive codimension-one subspace

This finite-dimensional Sylvester-inertia theorem closes the counting step
once the compared Schur quadratic form has a certified positive subspace of
codimension one and a negative trial direction. The separate passage from
physical matrix inequalities to the quadratic-form hypotheses, and the
infinite-dimensional operator-domain transfer, remain explicit obligations.
-/

namespace YangMillsInertiaComparison

/-- A real finite quadratic form that is strictly positive on a codimension-one
subspace and strictly negative on a one-dimensional subspace has exactly one
negative direction and a zero-dimensional radical. In particular, there is no
zero mode. The signs can come from the ordered Schur comparisons in
`SchurInertiaComparison`; this theorem does not assume a vacuum vector. -/
theorem one_negative_index_of_opposite_subspaces
    {M : Type*} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
    (Q : QuadraticForm ℝ M) (V W : Subspace ℝ M)
    (hPositive : (Q.restrict V).PosDef)
    (hCodim : Module.finrank ℝ V + 1 = Module.finrank ℝ M)
    (hNegative : ((-Q).restrict W).PosDef)
    (hOne : Module.finrank ℝ W = 1) :
    sigNeg Q = 1 ∧ Module.finrank ℝ Q.radical = 0 := by
  have hPosBound : Module.finrank ℝ V ≤ sigPos Q :=
    le_sigPos_of_posDef hPositive
  have hNegBound : Module.finrank ℝ W ≤ sigNeg Q :=
    le_sigNeg_of_negDef hNegative
  have hSignature := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q)
  omega

end YangMillsInertiaComparison

#print axioms YangMillsInertiaComparison.one_negative_index_of_opposite_subspaces
