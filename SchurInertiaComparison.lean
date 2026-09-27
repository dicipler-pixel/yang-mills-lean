import LongestYangMillsChain
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Retaining directions through the Schur comparison

These finite sign transfers are the next step from a matrix lower comparison
to an inertia certificate. They do not yet identify the signature of an
infinite-dimensional operator or prove a gauge-theory mass gap.
-/

open Matrix

namespace YangMillsInertiaComparison

variable {r c : Type*} [Fintype r] [Fintype c] [DecidableEq r] [DecidableEq c]

/-- A positive subspace of a lower matrix comparison remains positive for the
actual Schur matrix. The columns of `T` may be the positive directions
produced by an exact LDLᵀ certificate; they need not be coordinate vectors. -/
theorem positive_subspace_mono
    (K S : Matrix r r ℝ) (T : Matrix r c ℝ)
    (hKS : K ≤ S)
    (hK : (Tᴴ * K * T).PosDef) :
    (Tᴴ * S * T).PosDef := by
  have hdiff : (S - K).PosSemidef := (sub_nonneg.mpr hKS).posSemidef
  have hcongr : (Tᴴ * (S - K) * T).PosSemidef :=
    hdiff.conjTranspose_mul_mul_same T
  have hsum : K + (S - K) = S := by abel
  have hdecomp : Tᴴ * S * T = Tᴴ * K * T + Tᴴ * (S - K) * T := by
    calc
      Tᴴ * S * T = Tᴴ * (K + (S - K)) * T := by rw [hsum]
      _ = Tᴴ * K * T + Tᴴ * (S - K) * T := by
        simp only [Matrix.mul_add, Matrix.add_mul]
  rw [hdecomp]
  exact hK.add_posSemidef hcongr

/-- An upper comparison preserves a strictly negative quadratic trial
direction. This is the other sign needed by the one-negative-direction
argument; the spectral counting step remains stated in the written proof. -/
theorem negative_trial_antitone
    (S A : Matrix r r ℝ) (x : r → ℝ)
    (hSA : S ≤ A)
    (hA : star x ⬝ᵥ (A *ᵥ x) < 0) :
    star x ⬝ᵥ (S *ᵥ x) < 0 := by
  have hdiff : (A - S).PosSemidef := (sub_nonneg.mpr hSA).posSemidef
  have hn := hdiff.dotProduct_mulVec_nonneg x
  have heq :
      star x ⬝ᵥ ((A - S) *ᵥ x) =
        (star x ⬝ᵥ (A *ᵥ x)) - (star x ⬝ᵥ (S *ᵥ x)) := by
    simp [Matrix.sub_mulVec, dotProduct_sub]
  rw [heq] at hn
  linarith

end YangMillsInertiaComparison

#print axioms YangMillsInertiaComparison.positive_subspace_mono
#print axioms YangMillsInertiaComparison.negative_trial_antitone
