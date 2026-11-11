import GaugeSupportSimpleFamily
open CategoryTheory GaugeSupport

-- False: the regular representation of `S₃` on `S₃ → ℂ` (dimension 6) is simple. Routing
-- through the proved `simple_of_isIrreducible` leaves the goal that it is irreducible, which is
-- false: the constant functions form a proper nonzero stable line (the trivial representation).
-- The negation is proved as `not_simple_regularRep_S3` / `not_isIrreducible_regularRep`.
example : Simple (FDRep.of (regularRep (Equiv.Perm (Fin 3)))) := by
  refine simple_of_isIrreducible _ ?_
