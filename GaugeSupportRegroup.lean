/-
GaugeSupportRegroup.lean — the SU(3) gauge support rule regrouped by vertex
(Grey, 2026-11-11).

Setting (as in `GaugeSupportLattice.lean`): a finite oriented graph `Γ`, a labelling
`π : E → Irr` of the links by irreps `irr i : FDRep k G`, and at each vertex `v` the
vertex space `W_v(π) = vertexRep (incident Γ (irr ∘ π) v)`. The gauge group is `Vx → G`
(one copy of `G` per vertex); it acts on the vertex-regrouped block
`⨂_v W_v(π)` (Mathlib's `PiTensorProduct`) factor by factor, the `v`-th copy on `W_v(π)`.

Proved here (any group `G`, any field `k`; no algebraic closure, no compactness, no
complete reducibility, no finite dimensionality):
* `lTensor_fixed_eq_zero`: if `A^G = 0` then a vector of `B ⊗ A` fixed by every
  `id ⊗ ρ g` is zero (coordinates in a basis of `B`).
* `regroup_split_map`: splitting `⨂_w W_w ≅ (⨂_{w ≠ v} W_w) ⊗ W_v` intertwines a factorwise
  map with the corresponding pair of maps.
* `gauge_invariant_eq_zero_of_vertex`: if one vertex space has no nonzero invariant, the only
  gauge-invariant vector of `⨂_v W_v` is `0`.
* `vertex_invariant_ne_bot_of_gauge_invariant`: a nonzero gauge-invariant vector of
  `⨂_v W_v` forces a nonzero invariant in every `W_v`. This is the half of
  `(⨂_v W_v)^{G^V} = ⨂_v W_v^G` the support rule needs.
* `tprod_gauge_invariant`: conversely, a pure tensor of vertex invariants is gauge invariant.
* `support_vertex_invariant`: for a gauge-invariant state `ψ` of a lattice Hilbert space
  satisfying the named Peter–Weyl assumption, every labelling `π` with `ψ_π ≠ 0` has a
  nonzero invariant at every vertex.
* `gauge_support_rule_regrouped` (and `_SU3`): the per-vertex rule of
  `lattice_support_rule_of_simple` holds for every `π ∈ supp ψ`, with its per-vertex
  nonvanishing hypothesis discharged.

Named assumption (a structure, NOT an axiom): `PeterWeylLattice` / `PeterWeylSU3`. It says
the lattice Hilbert space `H` with gauge action `gauge` has, for every labelling `π`, a
block projection `proj π : H → ⨂_v W_v(π)` that is gauge-equivariant, and that the blocks
separate points (`ψ = 0` iff every `ψ_π = 0`). This is the Peter–Weyl decomposition
`L²(G) = ⊕_π V_π ⊗ V_π*` applied link by link, *together with* the reshuffle of tensor
factors `⊗_e (V_{π e} ⊗ V_{π e}*) ≅ ⊗_v W_v(π)` (outgoing link ↦ `V`, incoming link ↦ `V*`).
The reshuffle is a pure permutation of tensor factors; it is packaged in the assumption
and is NOT proved here.
No `sorry`, no `native_decide`, no new axioms. Checked on Lean v4.33.0 / Mathlib v4.33.0.
-/
import DualSimple
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Complex.Basic

open CategoryTheory MonoidalCategory Module TensorProduct

namespace GaugeSupport

universe u v

/-! ### One factor: invariants under `id ⊗ ρ` -/

section OneFactor

variable {k : Type*} {G : Type*} [Field k] [Group G]
  {A B : Type*} [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]

theorem lid_rTensor_lTensor (φ : B →ₗ[k] k) (f : A →ₗ[k] A) (x : B ⊗[k] A) :
    TensorProduct.lid k A (φ.rTensor A (f.lTensor B x)) =
      f (TensorProduct.lid k A (φ.rTensor A x)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b a => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- If `A` has no nonzero `G`-invariant, then neither does `B ⊗ A` with `G` acting on the
second factor only. Any field; `B` arbitrary (a basis of `B` gives coordinates in `A`). -/
theorem lTensor_fixed_eq_zero (ρ : Representation k G A)
    (hA : Representation.invariants ρ = ⊥) (x : B ⊗[k] A)
    (hx : ∀ g : G, (ρ g).lTensor B x = x) : x = 0 := by
  classical
  let b := Basis.ofVectorSpace k B
  apply (equivFinsuppOfBasisLeft b).injective
  ext i
  rw [equivFinsuppOfBasisLeft_apply, map_zero, Finsupp.zero_apply]
  have hmem : TensorProduct.lid k A ((b.coord i).rTensor A x) ∈
      Representation.invariants ρ := by
    intro g
    rw [← lid_rTensor_lTensor, hx g]
  rw [hA] at hmem
  exact (Submodule.mem_bot k).1 hmem

end OneFactor

/-! ### Many factors: the vertex-regrouped block `⨂_v W_v` -/

section ManyFactors

variable {k : Type*} {G : Type*} [Field k] [Group G]
  {Vx : Type*}
  (W : Vx → Type*) [∀ v, AddCommGroup (W v)] [∀ v, Module k (W v)]
  (ρ : ∀ v, Representation k G (W v))

/-- The gauge action of `Vx → G` on `⨂_v W v`: the `v`-th copy of `G` acts on `W v`. -/
noncomputable def gaugeAction : Representation k (Vx → G) (⨂[k] v, W v) :=
  PiTensorProduct.mapMonoidHom.comp
    (MonoidHom.pi fun v => (ρ v).comp (Pi.evalMonoidHom (fun _ : Vx => G) v))

theorem gaugeAction_apply (g : Vx → G) :
    gaugeAction W ρ g = PiTensorProduct.map (fun v => ρ v (g v)) := rfl

/-- Gauge-invariant vectors of the regrouped block. -/
def IsGaugeInvariant (t : ⨂[k] v, W v) : Prop := ∀ g : Vx → G, gaugeAction W ρ g t = t

/-- Splitting off the factor at `v` intertwines factorwise maps. -/
theorem regroup_split_map [DecidableEq Vx] (v : Vx) (f : ∀ w, W w →ₗ[k] W w) (t : ⨂[k] w, W w) :
    PiTensorProduct.equivPiTensorComplSingletonTensor k W v (PiTensorProduct.map f t) =
      TensorProduct.map (PiTensorProduct.map fun j : ({v}ᶜ : Set Vx) => f j) (f v)
        (PiTensorProduct.equivPiTensorComplSingletonTensor k W v t) := by
  have h : (PiTensorProduct.equivPiTensorComplSingletonTensor k W v).toLinearMap ∘ₗ
      PiTensorProduct.map f =
      TensorProduct.map (PiTensorProduct.map fun j : ({v}ᶜ : Set Vx) => f j) (f v) ∘ₗ
        (PiTensorProduct.equivPiTensorComplSingletonTensor k W v).toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro m
    simp [PiTensorProduct.map_tprod]
    rfl
  exact LinearMap.congr_fun h t

/-- **Regrouped invariants, vanishing form.** If the vertex space at `v` has no nonzero
`G`-invariant, the only gauge-invariant vector of `⨂_w W_w` is `0`. -/
theorem gauge_invariant_eq_zero_of_vertex [DecidableEq Vx] (t : ⨂[k] w, W w)
    (ht : IsGaugeInvariant W ρ t) (v : Vx) (hv : Representation.invariants (ρ v) = ⊥) :
    t = 0 := by
  let e := PiTensorProduct.equivPiTensorComplSingletonTensor k W v
  suffices h : e t = 0 by simpa using congrArg e.symm h
  apply lTensor_fixed_eq_zero (ρ v) hv
  intro g
  have h1 := regroup_split_map W v (fun w => ρ w ((Pi.mulSingle v g : Vx → G) w)) t
  have h2 := ht (Pi.mulSingle v g)
  rw [gaugeAction_apply] at h2
  rw [h2] at h1
  have h3 : (fun j : ({v}ᶜ : Set Vx) => ρ j ((Pi.mulSingle v g : Vx → G) (j : Vx))) =
      fun _ => (1 : _ →ₗ[k] _) := by
    funext j
    rw [Pi.mulSingle_eq_of_ne (show (j : Vx) ≠ v from j.2), map_one]
  refine Eq.trans ?_ h1.symm
  rw [h3, PiTensorProduct.map_one, Pi.mulSingle_eq_same]
  rfl

/-- **Regrouped invariants, support form.** A nonzero gauge-invariant vector of the
vertex-regrouped block forces a nonzero `G`-invariant in every vertex space. -/
theorem vertex_invariant_ne_bot_of_gauge_invariant [DecidableEq Vx] (t : ⨂[k] w, W w)
    (ht : IsGaugeInvariant W ρ t) (ht0 : t ≠ 0) (v : Vx) :
    Representation.invariants (ρ v) ≠ ⊥ :=
  fun hv => ht0 (gauge_invariant_eq_zero_of_vertex W ρ t ht v hv)

/-- Conversely, a pure tensor of vertex invariants is gauge invariant. -/
theorem tprod_gauge_invariant (x : ∀ v, W v)
    (hx : ∀ v, x v ∈ Representation.invariants (ρ v)) :
    IsGaugeInvariant W ρ (PiTensorProduct.tprod k x) := by
  intro g
  rw [gaugeAction_apply, PiTensorProduct.map_tprod]
  congr 1
  funext v
  exact hx v (g v)

end ManyFactors

/-! ### The lattice: named Peter–Weyl assumption and the regrouped support rule -/

section Lattice

variable {k : Type u} {G : Type v} [Field k] [Group G]
  {Vx E : Type*} [Fintype E]

/-- The vertex space `W_v(π)` of a labelling, as a type. -/
abbrev VertexSpace (Γ : OrientedGraph Vx E) (π : E → FDRep k G) (v : Vx) : Type u :=
  vertexRep (incident Γ π v)

/-- The vertex-regrouped block `⨂_v W_v(π)` of a labelling `π`. -/
abbrev RegroupedBlock (Γ : OrientedGraph Vx E) (π : E → FDRep k G) : Type _ :=
  ⨂[k] v, VertexSpace Γ π v

/-- The gauge action of `Vx → G` on the regrouped block of `π`. -/
noncomputable abbrev blockGauge (Γ : OrientedGraph Vx E) (π : E → FDRep k G) :
    Representation k (Vx → G) (RegroupedBlock Γ π) :=
  gaugeAction (VertexSpace Γ π) (fun v => (vertexRep (incident Γ π v)).ρ)

/-- **Named assumption (Peter–Weyl, regrouped by vertex).** A lattice Hilbert space `H`
with gauge action `gauge : Representation k (Vx → G) H` decomposes over labellings
`π : E → Irr` of the links by the irreps `irr`: each block projection
`proj π : H → ⨂_v W_v(π)` is gauge-equivariant, and the blocks separate points. For
`G = SU(3)`, `k = ℂ`, `H = ⊗_e L²(SU(3))` this is Peter–Weyl link by link plus the
reshuffle `⊗_e (V_{π e} ⊗ V_{π e}*) ≅ ⊗_v W_v(π)`; both are assumed, not proved. -/
structure PeterWeylLattice (k : Type u) (G : Type v) [Field k] [Group G]
    (Γ : OrientedGraph Vx E) (Irr : Type*) (irr : Irr → FDRep k G)
    (H : Type*) [AddCommGroup H] [Module k H] (gauge : Representation k (Vx → G) H) where
  /-- The component `ψ_π` of a state in the block of the labelling `π`. -/
  proj : ∀ π : E → Irr, H →ₗ[k] RegroupedBlock Γ (irr ∘ π)
  /-- Gauge transformations act block by block, the `v`-th copy of `G` on `W_v(π)`. -/
  proj_equivariant : ∀ (π : E → Irr) (g : Vx → G) (ψ : H),
    proj π (gauge g ψ) = blockGauge Γ (irr ∘ π) g (proj π ψ)
  /-- A state is determined by its components. -/
  proj_separating : ∀ ψ : H, (∀ π, proj π ψ = 0) → ψ = 0

/-- The model block sum `Π_π ⨂_v W_v(π)` with the blockwise gauge action. -/
noncomputable def piGauge (Γ : OrientedGraph Vx E) (Irr : Type*) (irr : Irr → FDRep k G) :
    Representation k (Vx → G) (∀ π : E → Irr, RegroupedBlock Γ (irr ∘ π)) where
  toFun g := LinearMap.pi fun π => blockGauge Γ (irr ∘ π) g ∘ₗ LinearMap.proj π
  map_one' := LinearMap.ext fun ψ => funext fun π => by simp
  map_mul' g h := LinearMap.ext fun ψ => funext fun π => by simp [map_mul]

/-- **Consistency of the named assumption**: the block-sum model satisfies
`PeterWeylLattice`, so the assumption is not vacuous. -/
noncomputable def PeterWeylLattice.model (Γ : OrientedGraph Vx E) (Irr : Type*)
    (irr : Irr → FDRep k G) :
    PeterWeylLattice k G Γ Irr irr (∀ π : E → Irr, RegroupedBlock Γ (irr ∘ π))
      (piGauge Γ Irr irr) where
  proj π := LinearMap.proj π
  proj_equivariant _ _ _ := rfl
  proj_separating _ h := funext h

/-- `SU(3)` as a group. -/
abbrev SU3 : Type := Matrix.specialUnitaryGroup (Fin 3) ℂ

/-- **`PeterWeylSU3`**: the named Peter–Weyl assumption for `SU(3)` over `ℂ`. -/
abbrev PeterWeylSU3 (Γ : OrientedGraph Vx E) (Irr : Type*) (irr : Irr → FDRep ℂ SU3)
    (H : Type*) [AddCommGroup H] [Module ℂ H] (gauge : Representation ℂ (Vx → SU3) H) :=
  PeterWeylLattice ℂ SU3 Γ Irr irr H gauge

/-- The support of a state: labellings whose component is nonzero. -/
def PeterWeylLattice.InSupport {Γ : OrientedGraph Vx E} {Irr : Type*} {irr : Irr → FDRep k G}
    {H : Type*} [AddCommGroup H] [Module k H] {gauge : Representation k (Vx → G) H}
    (PW : PeterWeylLattice k G Γ Irr irr H gauge) (ψ : H) (π : E → Irr) : Prop :=
  PW.proj π ψ ≠ 0

/-- The component of a gauge-invariant state is gauge invariant in its regrouped block. -/
theorem proj_gauge_invariant {Γ : OrientedGraph Vx E} {Irr : Type*} {irr : Irr → FDRep k G}
    {H : Type*} [AddCommGroup H] [Module k H] {gauge : Representation k (Vx → G) H}
    (PW : PeterWeylLattice k G Γ Irr irr H gauge) (ψ : H) (hψ : ∀ g, gauge g ψ = ψ)
    (π : E → Irr) :
    IsGaugeInvariant (VertexSpace Γ (irr ∘ π)) (fun v => (vertexRep (incident Γ (irr ∘ π) v)).ρ)
      (PW.proj π ψ) := by
  intro g
  rw [← PW.proj_equivariant, hψ g]

/-- **Regrouping by vertex: every vertex of a support carries a nonzero invariant.**
Under the named Peter–Weyl assumption, if `ψ` is gauge invariant and its component in
the block of `π` is nonzero, then every vertex space `W_v(π)` has a nonzero invariant. -/
theorem support_vertex_invariant [DecidableEq Vx] {Γ : OrientedGraph Vx E} {Irr : Type*}
    {irr : Irr → FDRep k G} {H : Type*} [AddCommGroup H] [Module k H]
    {gauge : Representation k (Vx → G) H} (PW : PeterWeylLattice k G Γ Irr irr H gauge)
    (ψ : H) (hψ : ∀ g, gauge g ψ = ψ) (π : E → Irr) (hπ : PW.proj π ψ ≠ 0) (v : Vx) :
    Representation.invariants (vertexRep (incident Γ (irr ∘ π) v)).ρ ≠ ⊥ :=
  vertex_invariant_ne_bot_of_gauge_invariant _ _ _ (proj_gauge_invariant PW ψ hψ π) hπ v

/-- A nonzero gauge-invariant state has nonempty support. -/
theorem support_nonempty {Γ : OrientedGraph Vx E} {Irr : Type*}
    {irr : Irr → FDRep k G} {H : Type*} [AddCommGroup H] [Module k H]
    {gauge : Representation k (Vx → G) H} (PW : PeterWeylLattice k G Γ Irr irr H gauge)
    (ψ : H) (hψ0 : ψ ≠ 0) : ∃ π, PW.proj π ψ ≠ 0 := by
  by_contra h
  push Not at h
  exact hψ0 (PW.proj_separating ψ h)

/-- **Gauge support rule, regrouped by vertex.** Under the named Peter–Weyl assumption,
with every irrep `irr i` simple: for a gauge-invariant state `ψ` and any labelling `π`
in its support, at every vertex `v` (a) the non-trivial incident links are not exactly
one, and (b) if they are exactly two, `x, y`, the two-valent pass-through holds. The
per-vertex nonvanishing hypothesis of `lattice_support_rule_of_simple` is discharged. -/
theorem gauge_support_rule_regrouped [DecidableEq Vx] {Γ : OrientedGraph Vx E} {Irr : Type*}
    {irr : Irr → FDRep k G} [∀ i, Simple (irr i)] {H : Type*} [AddCommGroup H] [Module k H]
    {gauge : Representation k (Vx → G) H} (PW : PeterWeylLattice k G Γ Irr irr H gauge)
    (ψ : H) (hψ : ∀ g, gauge g ψ = ψ) (π : E → Irr) (hπ : PW.proj π ψ ≠ 0) (v : Vx) :
    (∀ x, ntList (incident Γ (irr ∘ π) v) ≠ [x]) ∧
    (∀ x y, ntList (incident Γ (irr ∘ π) v) = [x, y] →
      (x.out = true → y.out = false → Nonempty (x.rep ≅ y.rep)) ∧
      (x.out = false → y.out = true → Nonempty (x.rep ≅ y.rep)) ∧
      (x.out = true → y.out = true → Nonempty (x.repᘁ ≅ y.rep)) ∧
      (x.out = false → y.out = false → Nonempty (x.rep ≅ y.repᘁ))) :=
  lattice_support_rule_of_simple (hs := fun e => (inferInstance : Simple (irr (π e))))
    Γ (irr ∘ π) (support_vertex_invariant PW ψ hψ π hπ) v

/-- **`gauge_support_rule_regrouped` for `SU(3)`**, under the named assumption
`PeterWeylSU3`. -/
theorem gauge_support_rule_regrouped_SU3 [DecidableEq Vx] {Γ : OrientedGraph Vx E} {Irr : Type*}
    {irr : Irr → FDRep ℂ SU3} [∀ i, Simple (irr i)] {H : Type*} [AddCommGroup H]
    [Module ℂ H] {gauge : Representation ℂ (Vx → SU3) H}
    (PW : PeterWeylSU3 Γ Irr irr H gauge)
    (ψ : H) (hψ : ∀ g, gauge g ψ = ψ) (π : E → Irr) (hπ : PW.proj π ψ ≠ 0) (v : Vx) :
    (∀ x, ntList (incident Γ (irr ∘ π) v) ≠ [x]) ∧
    (∀ x y, ntList (incident Γ (irr ∘ π) v) = [x, y] →
      (x.out = true → y.out = false → Nonempty (x.rep ≅ y.rep)) ∧
      (x.out = false → y.out = true → Nonempty (x.rep ≅ y.rep)) ∧
      (x.out = true → y.out = true → Nonempty (x.repᘁ ≅ y.rep)) ∧
      (x.out = false → y.out = false → Nonempty (x.rep ≅ y.repᘁ))) :=
  gauge_support_rule_regrouped PW ψ hψ π hπ v

end Lattice

end GaugeSupport

#print axioms GaugeSupport.lTensor_fixed_eq_zero
#print axioms GaugeSupport.regroup_split_map
#print axioms GaugeSupport.gauge_invariant_eq_zero_of_vertex
#print axioms GaugeSupport.vertex_invariant_ne_bot_of_gauge_invariant
#print axioms GaugeSupport.tprod_gauge_invariant
#print axioms GaugeSupport.support_vertex_invariant
#print axioms GaugeSupport.gauge_support_rule_regrouped
#print axioms GaugeSupport.gauge_support_rule_regrouped_SU3
