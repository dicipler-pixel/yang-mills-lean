import GaugeSupportRegroup
open CategoryTheory GaugeSupport
-- False: the regrouped SU(3) support rule needs a gauge-invariant state. Dropping
-- `hψ` leaves the goal `∀ g, gauge g ψ = ψ` open, which fails for a non-invariant state.
example {Vx E : Type} [DecidableEq Vx] [Fintype E] (Γ : OrientedGraph Vx E) (Irr : Type)
    (irr : Irr → FDRep ℂ SU3) [∀ i, Simple (irr i)]
    (ψ : ∀ π : E → Irr, RegroupedBlock Γ (irr ∘ π)) (π : E → Irr) (hπ : ψ π ≠ 0) (v : Vx) :
    ∀ x, ntList (incident Γ (irr ∘ π) v) ≠ [x] := by
  refine (gauge_support_rule_regrouped_SU3 (PeterWeylLattice.model Γ Irr irr) ψ ?_ π hπ v).1
