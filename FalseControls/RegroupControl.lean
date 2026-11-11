import GaugeSupportRegroup
open GaugeSupport
-- False: without a vertex whose invariants vanish, a gauge-invariant vector need not be
-- zero (one vertex, trivial representation on `ℚ`: every vector is gauge invariant), so
-- `gauge_invariant_eq_zero_of_vertex` cannot be applied: the goal
-- `invariants 1 = ⊥` stays open (it is false: the invariants are all of `ℚ`).
example (t : PiTensorProduct ℚ (fun _ : Fin 1 => ℚ))
    (ht : IsGaugeInvariant (fun _ : Fin 1 => ℚ) (fun _ => (1 : Representation ℚ Unit ℚ)) t) :
    t = 0 := by
  refine gauge_invariant_eq_zero_of_vertex _ _ t ht 0 ?_
