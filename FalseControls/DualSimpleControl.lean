import DualSimple
open CategoryTheory MonoidalCategory
-- False: without `[Simple V]` the dual need not be simple (the zero representation is a
-- counterexample), so `dual_simple` cannot be applied: the goal `Simple V` stays open.
example (V : FDRep ℚ Unit) : Simple Vᘁ := by
  refine @GaugeSupport.dual_simple ℚ Unit _ _ V ?_
