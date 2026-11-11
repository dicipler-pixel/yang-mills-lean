import ThetaTriality

/-!
# Cut bound from triality (Lean Green, 2026-11-11)

If `d` cuts each carry an irrep of nonzero triality, the electric cost is at
least `(4/3)·d`. In the `cas3 = 3·C₂` units of `ThetaFloor`, that is `4·d`.
The bound is tight: the fundamental `3` and antifundamental `3̄` cost exactly 4.

What this does NOT show: that a given lattice state must carry nonzero triality
through `d` disjoint cuts. That is the Gauss-law/flux-sector input and is
stated here as a hypothesis on the list of cut labels.
-/

namespace CutBound

open ThetaFloor ThetaTriality

/-- Any nonzero-triality irrep has `cas3 ≥ 4`, i.e. `C₂ ≥ 4/3`. -/
theorem cas3_ge_four_of_triality_ne (x : Irrep) (h : triality x ≠ 0) : 4 ≤ cas3 x := by
  obtain ⟨p, q⟩ := x
  cases p with
  | zero =>
    cases q with
    | zero => exact absurd rfl h
    | succ m =>
      have : 1 ≤ (m+1)*(m+1) := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
      simp only [cas3]; omega
  | succ n =>
    have : 1 ≤ (n+1)*(n+1) := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
    simp only [cas3]; omega

/-- The bound is attained by `3`. -/
theorem cas3_fund : cas3 (1, 0) = 4 := by decide

/-- The bound is attained by `3̄`. -/
theorem cas3_antifund : cas3 (0, 1) = 4 := by decide

/-- `d` cuts, each with nonzero triality, cost at least `4·d` in `cas3` units,
i.e. `(4/3)·d` in `C₂`. -/
theorem cut_bound (cuts : List Irrep) (h : ∀ x ∈ cuts, triality x ≠ 0) :
    4 * cuts.length ≤ (cuts.map cas3).sum := by
  induction cuts with
  | nil => simp
  | cons x xs ih =>
    have hx := cas3_ge_four_of_triality_ne x (h x (List.mem_cons_self ..))
    have hxs := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

/-- Tightness: `d` copies of the fundamental cost exactly `4·d`. -/
theorem cut_bound_tight (d : Nat) :
    ((List.replicate d ((1, 0) : Irrep)).map cas3).sum = 4 * d := by
  induction d with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ, List.map_cons, List.sum_cons] at *
    rw [ih, cas3_fund]; omega

end CutBound
