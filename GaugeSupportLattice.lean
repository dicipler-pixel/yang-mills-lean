/-
GaugeSupportLattice.lean — lattice form of the gauge support rule (Red, 2026-11-10).

Setting: a finite oriented graph `Γ` (loops and multi-edges allowed) with a
finite-dimensional representation `π e` on every edge. At a vertex `v`, an outgoing edge
contributes `π e` and an incoming edge `(π e)ᘁ`. The vertex space is the right-nested
tensor product of these factors, in the order of `incident Γ π v`.

Proved (any group `G`, any field `k`; no algebraic closure needed):
* `vertex_no_dangling`: exactly one non-trivial incident edge ⇒ no nonzero vertex invariant.
* `vertex_two_valent`: exactly two non-trivial incident edges and a nonzero invariant ⇒
  (in/out) the irreps are isomorphic, or (same orientation) one is the dual of the other.
* `lattice_support_rule`: both statements at every vertex, assuming each vertex space has
  a nonzero invariant.
Trivial edges are dropped with `𝟙 ⊗ X ≅ X`. The dual of a trivial representation is
proved trivial, and conversely, by uniqueness of duals. The two-edge case uses the rigid
adjunction `Hom(𝟙, Y ⊗ Z) ≃ₗ Hom(Y', Z)` for an exact pairing `(Y, Y')`, then Schur
(`isIso_of_hom_simple`).

Hypotheses that are NOT proved here:
* Simplicity of the duals `(π e)ᘁ`. This is true mathematically but not in Mathlib v4.33.0.
* Per-vertex nonvanishing. The bridge "gauge-invariant ψ with ψ_π ≠ 0 ⇒ every vertex
  space of π has a nonzero invariant" needs the regrouping of `⊗_e (V_e ⊗ V_e*)` into
  `⊗_v W_v` and `(⊗_v W_v)^{G^V} = ⊗_v W_v^G`. It also needs the Peter–Weyl
  decomposition of `L²(SU(3))`. All of these are on paper only
  (research/gauge_support_2026_11_10/GAUGE_SUPPORT_RULE.md).
No `sorry`, no `native_decide`, no new axioms. Checked on Lean v4.33.0 / Mathlib v4.33.0.
-/
import GaugeSupportFDRep

open CategoryTheory MonoidalCategory Module

namespace GaugeSupport

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G]

/-- `tensorLeftHomEquiv` is `k`-linear in `FDRep k G`. -/
noncomputable def tensorLeftHomLinearEquiv (X Y Y' Z : FDRep k G) [ExactPairing Y Y'] :
    (Y' ⊗ X ⟶ Z) ≃ₗ[k] (X ⟶ Y ⊗ Z) :=
  { tensorLeftHomEquiv X Y Y' Z with
    map_add' := fun f g => by simp [tensorLeftHomEquiv]
    map_smul' := fun c f => by simp [tensorLeftHomEquiv] }

/-- Invariants transfer along isomorphisms. -/
noncomputable def invariantsCongr {X Y : FDRep k G} (i : X ≅ Y) :
    Representation.invariants X.ρ ≃ₗ[k] Representation.invariants Y.ρ :=
  invariantsEquivUnitHom X ≪≫ₗ Linear.homCongr k (Iso.refl _) i ≪≫ₗ
    (invariantsEquivUnitHom Y).symm

theorem invariants_eq_bot_iff_of_iso {X Y : FDRep k G} (i : X ≅ Y) :
    Representation.invariants X.ρ = ⊥ ↔ Representation.invariants Y.ρ = ⊥ := by
  rw [← Submodule.subsingleton_iff_eq_bot, ← Submodule.subsingleton_iff_eq_bot]
  exact (invariantsCongr i).toEquiv.subsingleton_congr

/-- If `Y ⊗ Z` has a nonzero invariant and `(Y, Y')` is an exact pairing, there is a
nonzero morphism `Y' ⟶ Z`; for simple `Y', Z` it is an isomorphism (Schur). -/
theorem iso_of_pair_invariant (Y Y' Z : FDRep k G) [ExactPairing Y Y'] [Simple Y'] [Simple Z]
    (h : Representation.invariants (Y ⊗ Z).ρ ≠ ⊥) : Nonempty (Y' ≅ Z) := by
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  let e := (invariantsEquivUnitHom (Y ⊗ Z)) ≪≫ₗ
    (tensorLeftHomLinearEquiv (𝟙_ (FDRep k G)) Y Y' Z).symm ≪≫ₗ
    Linear.homCongr k (ρ_ Y') (Iso.refl Z)
  have hne : e ⟨w, hw⟩ ≠ 0 := by
    intro h0
    apply hw0
    have := congrArg Subtype.val (e.injective (h0.trans (map_zero e).symm))
    simpa using this
  have : IsIso (e ⟨w, hw⟩) := isIso_of_hom_simple hne
  exact ⟨asIso (e ⟨w, hw⟩)⟩

/-- A trivial representation has a trivial dual. -/
noncomputable def dualIsoUnitOfIso {X : FDRep k G} (i : 𝟙_ (FDRep k G) ≅ X) :
    Xᘁ ≅ 𝟙_ (FDRep k G) :=
  letI : ExactPairing X (𝟙_ (FDRep k G)) := exactPairingCongrLeft i.symm
  rightDualIso (inferInstance : ExactPairing X Xᘁ) this

/-- Conversely, if the dual is trivial so is the representation. -/
noncomputable def isoUnitOfDualIso {X : FDRep k G} (i : Xᘁ ≅ 𝟙_ (FDRep k G)) :
    X ≅ 𝟙_ (FDRep k G) :=
  letI : ExactPairing X (𝟙_ (FDRep k G)) := exactPairingCongrRight i.symm
  letI p : ExactPairing (𝟙_ (FDRep k G)) X := BraidedCategory.exactPairing_swap X (𝟙_ (FDRep k G))
  rightDualIso p (inferInstance : ExactPairing (𝟙_ (FDRep k G)) (𝟙_ (FDRep k G)))

/-! ### Half-edges at a vertex and the vertex representation -/

/-- An edge end at a vertex: the irrep on the edge and whether the edge leaves the vertex
(`out = true`, contributes `rep`) or enters it (`out = false`, contributes `repᘁ`). -/
structure HalfEdge (k : Type u) (G : Type v) [Field k] [Group G] where
  rep : FDRep k G
  out : Bool

/-- The tensor factor a half-edge contributes at its vertex. -/
noncomputable def HalfEdge.factor (h : HalfEdge k G) : FDRep k G :=
  if h.out then h.rep else h.repᘁ

/-- Right-nested tensor product of a list, ending in `𝟙`. -/
noncomputable def tensorList : List (FDRep k G) → FDRep k G
  | [] => 𝟙_ (FDRep k G)
  | X :: l => X ⊗ tensorList l

/-- The vertex space `W_v = ⊗ (incident factors)`. -/
noncomputable def vertexRep (l : List (HalfEdge k G)) : FDRep k G :=
  tensorList (l.map HalfEdge.factor)

/-- A half-edge is non-trivial when its irrep is not the unit. -/
def HalfEdge.NT (h : HalfEdge k G) : Prop := IsEmpty (𝟙_ (FDRep k G) ≅ h.rep)

open scoped Classical in
/-- The non-trivial half-edges at a vertex, in order. -/
noncomputable def ntList (l : List (HalfEdge k G)) : List (HalfEdge k G) :=
  l.filter (fun h => decide h.NT)

theorem factor_out {h : HalfEdge k G} (hh : h.out = true) : h.factor = h.rep := by
  simp [HalfEdge.factor, hh]

theorem factor_in {h : HalfEdge k G} (hh : h.out = false) : h.factor = h.repᘁ := by
  simp [HalfEdge.factor, hh]

theorem factor_iso_unit_of_not_NT (h : HalfEdge k G) (hh : ¬ h.NT) :
    Nonempty (h.factor ≅ 𝟙_ (FDRep k G)) := by
  have : Nonempty (𝟙_ (FDRep k G) ≅ h.rep) := by
    by_contra hc; exact hh (not_nonempty_iff.mp hc)
  obtain ⟨i⟩ := this
  unfold HalfEdge.factor
  split
  · exact ⟨i.symm⟩
  · exact ⟨dualIsoUnitOfIso i⟩

theorem factor_not_iso_unit_of_NT (h : HalfEdge k G) (hh : h.NT) :
    IsEmpty (𝟙_ (FDRep k G) ≅ h.factor) := by
  constructor
  intro i
  unfold HalfEdge.factor at i
  split at i
  · exact hh.false i
  · exact hh.false (isoUnitOfDualIso i.symm).symm

/-- Trivial factors can be dropped: `W_v ≅ ⊗ (non-trivial factors)`. -/
theorem vertexRep_iso_ntList (l : List (HalfEdge k G)) :
    Nonempty (vertexRep l ≅ vertexRep (ntList l)) := by
  classical
  induction l with
  | nil => exact ⟨Iso.refl _⟩
  | cons a l ih =>
    obtain ⟨i⟩ := ih
    by_cases ha : a.NT
    · have : ntList (a :: l) = a :: ntList l := by
        simp [ntList, ha]
      rw [this]
      exact ⟨whiskerLeftIso a.factor i⟩
    · have : ntList (a :: l) = ntList l := by
        simp [ntList, ha]
      rw [this]
      obtain ⟨j⟩ := factor_iso_unit_of_not_NT a ha
      exact ⟨whiskerRightIso j _ ≪≫ λ_ _ ≪≫ i⟩

/-- **Vertex rule (a): no dangling link.** If exactly one incident half-edge is
non-trivial, the vertex space has no nonzero invariant. -/
theorem vertex_no_dangling (l : List (HalfEdge k G)) (x : HalfEdge k G)
    (hx : ntList l = [x]) [Simple x.factor] :
    Representation.invariants (vertexRep l).ρ = ⊥ := by
  obtain ⟨i⟩ := vertexRep_iso_ntList l
  rw [invariants_eq_bot_iff_of_iso i, hx]
  have hNT : x.NT := by
    have : x ∈ ntList l := by simp [hx]
    simpa [ntList] using (List.mem_filter.mp this).2
  have j : vertexRep [x] ≅ x.factor := ρ_ x.factor
  rw [invariants_eq_bot_iff_of_iso j]
  exact gauge_no_dangling x.factor (factor_not_iso_unit_of_NT x hNT)

/-- **Vertex rule (b): two-valent vertices.** If exactly two incident half-edges `x, y`
are non-trivial (in that order) and the vertex space has a nonzero invariant, then:
one out and one in ⇒ the irreps are isomorphic; both out ⇒ `y ≅ xᘁ`;
both in ⇒ `x ≅ yᘁ`. Simplicity of the irreps and of the duals that occur is assumed. -/
theorem vertex_two_valent (l : List (HalfEdge k G)) (x y : HalfEdge k G)
    (hxy : ntList l = [x, y]) [Simple x.rep] [Simple y.rep]
    (h : Representation.invariants (vertexRep l).ρ ≠ ⊥) :
    (x.out = true → y.out = false → Nonempty (x.rep ≅ y.rep)) ∧
    (x.out = false → y.out = true → Nonempty (x.rep ≅ y.rep)) ∧
    (x.out = true → y.out = true → [Simple x.repᘁ] → Nonempty (x.repᘁ ≅ y.rep)) ∧
    (x.out = false → y.out = false → [Simple y.repᘁ] → Nonempty (x.rep ≅ y.repᘁ)) := by
  obtain ⟨i⟩ := vertexRep_iso_ntList l
  rw [Ne, invariants_eq_bot_iff_of_iso i, hxy] at h
  have j : vertexRep [x, y] ≅ x.factor ⊗ y.factor := whiskerLeftIso x.factor (ρ_ y.factor)
  rw [invariants_eq_bot_iff_of_iso j] at h
  refine ⟨fun hx hy => ?_, fun hx hy => ?_, fun hx hy _ => ?_, fun hx hy _ => ?_⟩
  · -- x out, y in: `x ⊗ yᘁ ≅ yᘁ ⊗ x`; pairing `(yᘁ, y)`.
    rw [invariants_eq_bot_iff_of_iso
      ((eqToIso (factor_out hx) ⊗ᵢ eqToIso (factor_in hy)) ≪≫ β_ x.rep y.repᘁ)] at h
    let _ : ExactPairing y.repᘁ y.rep := BraidedCategory.exactPairing_swap y.rep y.repᘁ
    obtain ⟨e⟩ := iso_of_pair_invariant y.repᘁ y.rep x.rep h
    exact ⟨e.symm⟩
  · -- x in, y out: `xᘁ ⊗ y`; pairing `(xᘁ, x)`.
    rw [invariants_eq_bot_iff_of_iso (eqToIso (factor_in hx) ⊗ᵢ eqToIso (factor_out hy))] at h
    let _ : ExactPairing x.repᘁ x.rep := BraidedCategory.exactPairing_swap x.rep x.repᘁ
    exact iso_of_pair_invariant x.repᘁ x.rep y.rep h
  · -- both out: `x ⊗ y`; pairing `(x, xᘁ)`.
    rw [invariants_eq_bot_iff_of_iso (eqToIso (factor_out hx) ⊗ᵢ eqToIso (factor_out hy))] at h
    exact iso_of_pair_invariant x.rep x.repᘁ y.rep h
  · -- both in: `xᘁ ⊗ yᘁ`; pairing `(xᘁ, x)`.
    rw [invariants_eq_bot_iff_of_iso (eqToIso (factor_in hx) ⊗ᵢ eqToIso (factor_in hy))] at h
    let _ : ExactPairing x.repᘁ x.rep := BraidedCategory.exactPairing_swap x.rep x.repᘁ
    exact iso_of_pair_invariant x.repᘁ x.rep y.repᘁ h

/-! ### Lattice form: an oriented graph with an irrep on every edge -/

/-- A finite graph with oriented edges (loops and multi-edges allowed). -/
structure OrientedGraph (Vx : Type*) (E : Type*) where
  src : E → Vx
  tgt : E → Vx

open scoped Classical in
/-- The half-edges at `v`: outgoing edges contribute `π e`, incoming edges `(π e)ᘁ`. -/
noncomputable def incident {Vx E : Type*} [Fintype E] (Γ : OrientedGraph Vx E)
    (π : E → FDRep k G) (v : Vx) : List (HalfEdge k G) :=
  ((Finset.univ.filter (fun e => Γ.src e = v)).toList.map (fun e => ⟨π e, true⟩)) ++
    ((Finset.univ.filter (fun e => Γ.tgt e = v)).toList.map (fun e => ⟨π e, false⟩))

theorem rep_of_mem_ntList {Vx E : Type*} [Fintype E] (Γ : OrientedGraph Vx E)
    (π : E → FDRep k G) (v : Vx) {x : HalfEdge k G} (hx : x ∈ ntList (incident Γ π v)) :
    ∃ e, x.rep = π e := by
  classical
  simp only [ntList, List.mem_filter, incident, List.mem_append, List.mem_map] at hx
  rcases hx.1 with ⟨e, -, rfl⟩ | ⟨e, -, rfl⟩ <;> exact ⟨e, rfl⟩

theorem simple_factor (x : HalfEdge k G) [Simple x.rep] [Simple x.repᘁ] : Simple x.factor := by
  unfold HalfEdge.factor; split <;> infer_instance

/-- **Gauge support rule, lattice form.** Let every edge carry an irrep `π e` with `π e`
and `(π e)ᘁ` simple, and suppose the vertex space at every vertex has a nonzero
invariant. Then at every vertex `v`: (a) the non-trivial incident edges are not exactly
one; (b) if they are exactly two, `x, y` (in the order of `incident`), then one out and
one in ⇒ `x.rep ≅ y.rep`; both out ⇒ `x.repᘁ ≅ y.rep`; both in ⇒ `x.rep ≅ y.repᘁ`. -/
theorem lattice_support_rule {Vx E : Type*} [Fintype E] (Γ : OrientedGraph Vx E)
    (π : E → FDRep k G) [hs : ∀ e, Simple (π e)] [hd : ∀ e, Simple (π e)ᘁ]
    (hinv : ∀ v, Representation.invariants (vertexRep (incident Γ π v)).ρ ≠ ⊥) (v : Vx) :
    (∀ x, ntList (incident Γ π v) ≠ [x]) ∧
    (∀ x y, ntList (incident Γ π v) = [x, y] →
      (x.out = true → y.out = false → Nonempty (x.rep ≅ y.rep)) ∧
      (x.out = false → y.out = true → Nonempty (x.rep ≅ y.rep)) ∧
      (x.out = true → y.out = true → Nonempty (x.repᘁ ≅ y.rep)) ∧
      (x.out = false → y.out = false → Nonempty (x.rep ≅ y.repᘁ))) := by
  have hsx : ∀ x ∈ ntList (incident Γ π v), Simple x.rep ∧ Simple x.repᘁ := by
    intro x hx
    obtain ⟨e, he⟩ := rep_of_mem_ntList Γ π v hx
    rw [he]; exact ⟨hs e, hd e⟩
  refine ⟨fun x hx => ?_, fun x y hxy => ?_⟩
  · obtain ⟨h1, h2⟩ := hsx x (by simp [hx])
    have := simple_factor x
    exact hinv v (vertex_no_dangling _ x hx)
  · obtain ⟨hx1, hx2⟩ := hsx x (by simp [hxy])
    obtain ⟨hy1, hy2⟩ := hsx y (by simp [hxy])
    obtain ⟨a, b, c, d⟩ := vertex_two_valent _ x y hxy (hinv v)
    exact ⟨a, b, fun h1 h2 => c h1 h2, fun h1 h2 => d h1 h2⟩

end GaugeSupport

#print axioms GaugeSupport.vertex_no_dangling
#print axioms GaugeSupport.vertex_two_valent
#print axioms GaugeSupport.lattice_support_rule
