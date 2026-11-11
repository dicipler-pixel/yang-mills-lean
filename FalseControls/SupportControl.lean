import GaugeSupportRegroup
open CategoryTheory GaugeSupport
-- False: a labelling outside the support (here the zero state, every component `0`) need
-- not have a nonzero invariant at every vertex, so `support_vertex_invariant` cannot be
-- applied without `proj π ψ ≠ 0`: the goal `proj π 0 ≠ 0` stays open.
example {Vx E : Type} [DecidableEq Vx] [Fintype E] (Γ : OrientedGraph Vx E) (Irr : Type)
    (irr : Irr → FDRep ℚ Unit) (π : E → Irr) (v : Vx) :
    Representation.invariants (vertexRep (incident Γ (irr ∘ π) v)).ρ ≠ ⊥ := by
  refine support_vertex_invariant (PeterWeylLattice.model Γ Irr irr) 0 (by simp) π ?_ v
