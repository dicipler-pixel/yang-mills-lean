import GaugeSupportPeterWeylFinite
open CategoryTheory MonoidalCategory Module TensorProduct GaugeSupport

-- False: `PeterWeylLinks` for `S₃` on a single link with the family `{trivial}`, which omits
-- the sign representation (and the standard one). Routing through the proved
-- `peterWeylLinks_of_finite` leaves the completeness goal: every irreducible `σ` would have to
-- be isomorphic to the trivial representation. That is false (the sign representation is not),
-- and the negation is proved as `not_isCompleteIrrFamily_trivial_S3` /
-- `not_peterWeylLinks_trivial_only`. The goal stays open.
example : Nonempty (PeterWeylLinks ℂ (Equiv.Perm (Fin 3)) oneLinkGraph Unit
    (fun _ => trivFD (Equiv.Perm (Fin 3))) ((Unit → Equiv.Perm (Fin 3)) → ℂ)
    (latticeGauge oneLinkGraph)) := by
  refine peterWeylLinks_of_finite oneLinkGraph _ ?_
  intro W _ _ _ σ _
  refine ⟨(), ?_⟩
