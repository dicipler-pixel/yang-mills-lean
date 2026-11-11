import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic.Linarith

/-!
# KyFanChord: a gap floor along a chord from certified endpoint data

This is the inference step behind Green's Ky Fan chord certification
(`research/2026-11-11/kyfan_chord/`, PR #19). Lean checks only the algebra.

* Concavity of `κ ↦ E₀ κ + E₁ κ` on the chord is a **named hypothesis** (`hconc`).
  For a Hamiltonian `H(κ)` that is linear in `κ`, it follows from Ky Fan's theorem
  (the sum of the lowest two eigenvalues is a minimum of linear functions of κ).
  It is **not proved in Lean** here.
* The endpoint lower bounds `sa`, `sb` and the upper bounds on `E₀` are **inputs**:
  Green's exact node values and trial Rayleigh quotients in `kyfan_theta.json`.
  Lean does not recompute or check those numbers.
* The `E₀` upper bound may be any pointwise bound `u κ ≥ E₀ κ`, including a finite
  minimum of affine Rayleigh-quotient bounds (`chord_gap_lower_inf`).
-/

namespace KyFanChord

open Set

/-- The chord point `(1-t)a + tb` lies in `[a, b]` for `t ∈ [0,1]`. -/
theorem chord_mem {a b t : ℝ} (hab : a ≤ b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * a + t * b ∈ Icc a b := by
  constructor <;> nlinarith

/-- Main step. Concave `E₀+E₁` on `[a,b]`, certified lower bounds at the ends, and any
pointwise upper bound `u ≥ E₀` give a gap lower bound at every chord point. -/
theorem chord_gap_lower (E₀ E₁ u : ℝ → ℝ) {a b sa sb t : ℝ} (hab : a ≤ b)
    (hconc : ConcaveOn ℝ (Icc a b) (fun κ => E₀ κ + E₁ κ))
    (ha : sa ≤ E₀ a + E₁ a) (hb : sb ≤ E₀ b + E₁ b)
    (hu : ∀ κ ∈ Icc a b, E₀ κ ≤ u κ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * sa + t * sb - 2 * u ((1 - t) * a + t * b)
      ≤ E₁ ((1 - t) * a + t * b) - E₀ ((1 - t) * a + t * b) := by
  have hmem := chord_mem hab ht0 ht1
  have hc := hconc.2 (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
    (by linarith : (0:ℝ) ≤ 1 - t) ht0 (by ring : (1 - t) + t = 1)
  simp only [smul_eq_mul] at hc
  have h1 := hu _ hmem
  nlinarith

/-- Positivity form: if the chord expression is positive, so is the gap. -/
theorem chord_gap_pos (E₀ E₁ u : ℝ → ℝ) {a b sa sb t : ℝ} (hab : a ≤ b)
    (hconc : ConcaveOn ℝ (Icc a b) (fun κ => E₀ κ + E₁ κ))
    (ha : sa ≤ E₀ a + E₁ a) (hb : sb ≤ E₀ b + E₁ b)
    (hu : ∀ κ ∈ Icc a b, E₀ κ ≤ u κ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hpos : 0 < (1 - t) * sa + t * sb - 2 * u ((1 - t) * a + t * b)) :
    E₀ ((1 - t) * a + t * b) < E₁ ((1 - t) * a + t * b) := by
  have := chord_gap_lower E₀ E₁ u hab hconc ha hb hu ht0 ht1
  linarith

/-- Finite-minimum form, as Green uses it: `E₀` is bounded by each of finitely many
affine trial quotients `m i * κ + c i`, so by their minimum. -/
theorem chord_gap_lower_inf {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (m c : ι → ℝ) (E₀ E₁ : ℝ → ℝ) {a b sa sb t : ℝ} (hab : a ≤ b)
    (hconc : ConcaveOn ℝ (Icc a b) (fun κ => E₀ κ + E₁ κ))
    (ha : sa ≤ E₀ a + E₁ a) (hb : sb ≤ E₀ b + E₁ b)
    (hq : ∀ i ∈ s, ∀ κ ∈ Icc a b, E₀ κ ≤ m i * κ + c i)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * sa + t * sb - 2 * s.inf' hs (fun i => m i * ((1 - t) * a + t * b) + c i)
      ≤ E₁ ((1 - t) * a + t * b) - E₀ ((1 - t) * a + t * b) :=
  chord_gap_lower E₀ E₁ (fun κ => s.inf' hs (fun i => m i * κ + c i)) hab hconc ha hb
    (fun κ hκ => Finset.le_inf' hs _ (fun i hi => hq i hi κ hκ)) ht0 ht1

end KyFanChord
