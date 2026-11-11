import PermCube

/-!
# Gauge supports on the strip, corner, two-square and double-cube graphs

Author: Jeromie Beasley (Lean Green PR Machine, Grok Bot), with the Team.
ORCID https://orcid.org/0009-0006-4645-5643 · GitHub dicipler-pixel · X @d1c1pler ·
YouTube @AtlasMemoriae · atlas-memoriae.dicipler.workers.dev

This follows the `cubeΓ` pattern of `PermCube.lean`, made generic. `listΓ g n` is the
oriented graph on `Fin (n+1)` whose link `i` runs as the `i`-th pair of the TailFloor edge
list `g`, with `lab = Fin.val`. `list_gauge_support_shortCycle` and
`list_gauge_support_card` apply `PermCube.gauge_support_shortCycle_of_SSAC` to it, given two
`decide` checks (every link is in `g` with its orientation, and no two links share an end
pair), `simpleB g`, and `SmallSupportsAreCycles g`.

Instances, each under the named hypothesis `PeterWeylLattice` alone (every irrep simple),
for a gauge-invariant state and a labelling in its support with 1 to 6 non-trivial links:
* two squares (`twoE`, 6 vertices, 7 links; host predicate `TailFloor.two_cycles`);
* three-square strip (`stripE`, 8 vertices, 10 links; `TailFloor.strip_cycles`);
* corner (`cornerE`, 7 vertices, 9 links; `TailFloor.corner_cycles`);
* double cube (`dcubeE`, 12 vertices, 20 links; `SmallSupportBridge.dcube_cycles_of_codegree`,
  the colouring-and-codegree route of #23, with no support enumeration).
On each, the non-trivial links form a single connected 4- or 6-cycle
(`*_gauge_support_shortCycle`), so there are exactly 4 or 6 of them (`*_gauge_support_card`).
`dcube_gauge_support_card_ne_five` records that the double cube has no 5-link such support.
-/

open CategoryTheory TailFloor GaugeSupport SmallSupportBridge NtListSupport PermCube
open scoped Classical

namespace GraphInstances

universe u v

/-- Endpoint of link `i` of the edge list `g`, as a vertex of `Fin (n+1)`. -/
def listEnd (g : Graph) (n : ℕ) (i : Fin g.length) (first : Bool) : Fin (n + 1) :=
  ⟨(if first then g[i].1 else g[i].2) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩

/-- The oriented graph of an edge list: link `i` runs as the `i`-th pair of `g`. -/
def listΓ (g : Graph) (n : ℕ) : OrientedGraph (Fin (n + 1)) (Fin g.length) where
  src i := listEnd g n i true
  tgt i := listEnd g n i false

/-- Every link of `listΓ g n` is a pair of `g`, with its orientation. -/
def LinksIn (g : Graph) (n : ℕ) : Prop :=
  ∀ i : Fin g.length, (((listΓ g n).src i).val, ((listΓ g n).tgt i).val) ∈ g

/-- No two links of `listΓ g n` share an end pair. -/
def NormInj (g : Graph) (n : ℕ) : Prop :=
  ∀ i j : Fin g.length, norm (((listΓ g n).src i).val, ((listΓ g n).tgt i).val) =
    norm (((listΓ g n).src j).val, ((listΓ g n).tgt j).val) → i = j

/-- **Generic instance.** On `listΓ g n`, under `PeterWeylLattice` (every irrep simple), a
labelling in the support of a gauge-invariant state with 1 to 6 non-trivial links has them
forming a single connected 4- or 6-cycle, provided `LinksIn`, `NormInj`, `simpleB g` and
`SmallSupportsAreCycles g`. -/
theorem list_gauge_support_shortCycle {k : Type u} {G : Type v} [Field k] [Group G]
    (g : Graph) (n : ℕ) (hmem : LinksIn g n) (hinj : NormInj g n) (hs : simpleB g = true)
    (hSSAC : SmallSupportsAreCycles g)
    {Irr : Type*} {irr : Irr → FDRep k G} [∀ i, Simple (irr i)] {H : Type*} [AddCommGroup H]
    [Module k H] {gauge : Representation k (Fin (n + 1) → G) H}
    (PW : PeterWeylLattice k G (listΓ g n) Irr irr H gauge)
    (ψ : H) (hψ : ∀ g, gauge g ψ = ψ) (π : Fin g.length → Irr) (hπ : PW.proj π ψ ≠ 0)
    (h1 : 1 ≤ (Finset.univ.filter (NTe (irr ∘ π))).card)
    (h6 : (Finset.univ.filter (NTe (irr ∘ π))).card ≤ 6) :
    shortCycle (supportList (listΓ g n) (irr ∘ π) Fin.val) = true := by
  have hlen := supportList_length (listΓ g n) (irr ∘ π) Fin.val
  refine gauge_support_shortCycle_of_SSAC PW ψ hψ π hπ Fin.val Fin.val_injective
    (fun e e' _ _ h => hinj e e' h) g hs hSSAC ?_ ?_ (by omega)
  · intro p hp
    simp only [supportList, List.mem_map] at hp
    obtain ⟨e, -, rfl⟩ := hp
    exact hmem e
  · intro h; rw [h] at hlen; simp at hlen; omega

/-- **Generic instance, link count.** Under the same hypotheses there are exactly 4 or 6
non-trivial links. -/
theorem list_gauge_support_card {k : Type u} {G : Type v} [Field k] [Group G]
    (g : Graph) (n : ℕ) (hmem : LinksIn g n) (hinj : NormInj g n) (hs : simpleB g = true)
    (hSSAC : SmallSupportsAreCycles g)
    {Irr : Type*} {irr : Irr → FDRep k G} [∀ i, Simple (irr i)] {H : Type*} [AddCommGroup H]
    [Module k H] {gauge : Representation k (Fin (n + 1) → G) H}
    (PW : PeterWeylLattice k G (listΓ g n) Irr irr H gauge)
    (ψ : H) (hψ : ∀ g, gauge g ψ = ψ) (π : Fin g.length → Irr) (hπ : PW.proj π ψ ≠ 0)
    (h1 : 1 ≤ (Finset.univ.filter (NTe (irr ∘ π))).card)
    (h6 : (Finset.univ.filter (NTe (irr ∘ π))).card ≤ 6) :
    (Finset.univ.filter (NTe (irr ∘ π))).card = 4 ∨
      (Finset.univ.filter (NTe (irr ∘ π))).card = 6 := by
  have h := list_gauge_support_shortCycle g n hmem hinj hs hSSAC PW ψ hψ π hπ h1 h6
  rw [← supportList_length (listΓ g n) (irr ∘ π) Fin.val]
  unfold shortCycle at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact h.1.1

/-! ## The four graphs -/

/-- Two squares: vertices `0..5`. -/
abbrev twoΓ := listΓ twoE 5
/-- Three-square strip: vertices `0..7`. -/
abbrev stripΓ := listΓ stripE 7
/-- Corner (cube without vertex 7): vertices `0..6`. -/
abbrev cornerΓ := listΓ cornerE 6
/-- Double cube: vertices `0..11`. -/
abbrev dcubeΓ := listΓ dcubeE 11

theorem twoΓ_links : LinksIn twoE 5 := by unfold LinksIn; decide
theorem twoΓ_norm_inj : NormInj twoE 5 := by unfold NormInj; decide
theorem twoE_simple : simpleB twoE = true := by decide

theorem stripΓ_links : LinksIn stripE 7 := by unfold LinksIn; decide
theorem stripΓ_norm_inj : NormInj stripE 7 := by unfold NormInj; decide
theorem stripE_simple : simpleB stripE = true := by decide

theorem cornerΓ_links : LinksIn cornerE 6 := by unfold LinksIn; decide
theorem cornerΓ_norm_inj : NormInj cornerE 6 := by unfold NormInj; decide
theorem cornerE_simple : simpleB cornerE = true := by decide

theorem dcubeΓ_links : LinksIn dcubeE 11 := by unfold LinksIn; decide
theorem dcubeΓ_norm_inj : NormInj dcubeE 11 := by unfold NormInj; decide +kernel
theorem dcubeE_simple : simpleB dcubeE = true := by decide

section Instances

variable {k : Type u} {G : Type v} [Field k] [Group G]
  {Irr : Type*} {irr : Irr → FDRep k G} [∀ i, Simple (irr i)] {H : Type*} [AddCommGroup H]
  [Module k H]

theorem two_gauge_support_shortCycle {gauge : Representation k (Fin 6 → G) H}
    (PW : PeterWeylLattice k G twoΓ Irr irr H gauge)
    (ψ : H) (hψ : ∀ g, gauge g ψ = ψ) (π : Fin twoE.length → Irr) (hπ : PW.proj π ψ ≠ 0)
    (h1 : 1 ≤ (Finset.univ.filter (NTe (irr ∘ π))).card)
    (h6 : (Finset.univ.filter (NTe (irr ∘ π))).card ≤ 6) :
    shortCycle (supportList twoΓ (irr ∘ π) Fin.val) = true :=
  list_gauge_support_shortCycle twoE 5 twoΓ_links twoΓ_norm_inj twoE_simple two_cycles
    PW ψ hψ π hπ h1 h6

theorem two_gauge_support_card {gauge : Representation k (Fin 6 → G) H}
    (PW : PeterWeylLattice k G twoΓ Irr irr H gauge)
    (ψ : H) (hψ : ∀ g, gauge g ψ = ψ) (π : Fin twoE.length → Irr) (hπ : PW.proj π ψ ≠ 0)
    (h1 : 1 ≤ (Finset.univ.filter (NTe (irr ∘ π))).card)
    (h6 : (Finset.univ.filter (NTe (irr ∘ π))).card ≤ 6) :
    (Finset.univ.filter (NTe (irr ∘ π))).card = 4 ∨
      (Finset.univ.filter (NTe (irr ∘ π))).card = 6 :=
  list_gauge_support_card twoE 5 twoΓ_links twoΓ_norm_inj twoE_simple two_cycles
    PW ψ hψ π hπ h1 h6

theorem strip_gauge_support_shortCycle {gauge : Representation k (Fin 8 → G) H}
    (PW : PeterWeylLattice k G stripΓ Irr irr H gauge)
    (ψ : H) (hψ : ∀ g, gauge g ψ = ψ) (π : Fin stripE.length → Irr) (hπ : PW.proj π ψ ≠ 0)
    (h1 : 1 ≤ (Finset.univ.filter (NTe (irr ∘ π))).card)
    (h6 : (Finset.univ.filter (NTe (irr ∘ π))).card ≤ 6) :
    shortCycle (supportList stripΓ (irr ∘ π) Fin.val) = true :=
  list_gauge_support_shortCycle stripE 7 stripΓ_links stripΓ_norm_inj stripE_simple strip_cycles
    PW ψ hψ π hπ h1 h6

theorem strip_gauge_support_card {gauge : Representation k (Fin 8 → G) H}
    (PW : PeterWeylLattice k G stripΓ Irr irr H gauge)
    (ψ : H) (hψ : ∀ g, gauge g ψ = ψ) (π : Fin stripE.length → Irr) (hπ : PW.proj π ψ ≠ 0)
    (h1 : 1 ≤ (Finset.univ.filter (NTe (irr ∘ π))).card)
    (h6 : (Finset.univ.filter (NTe (irr ∘ π))).card ≤ 6) :
    (Finset.univ.filter (NTe (irr ∘ π))).card = 4 ∨
      (Finset.univ.filter (NTe (irr ∘ π))).card = 6 :=
  list_gauge_support_card stripE 7 stripΓ_links stripΓ_norm_inj stripE_simple strip_cycles
    PW ψ hψ π hπ h1 h6

theorem corner_gauge_support_shortCycle {gauge : Representation k (Fin 7 → G) H}
    (PW : PeterWeylLattice k G cornerΓ Irr irr H gauge)
    (ψ : H) (hψ : ∀ g, gauge g ψ = ψ) (π : Fin cornerE.length → Irr) (hπ : PW.proj π ψ ≠ 0)
    (h1 : 1 ≤ (Finset.univ.filter (NTe (irr ∘ π))).card)
    (h6 : (Finset.univ.filter (NTe (irr ∘ π))).card ≤ 6) :
    shortCycle (supportList cornerΓ (irr ∘ π) Fin.val) = true :=
  list_gauge_support_shortCycle cornerE 6 cornerΓ_links cornerΓ_norm_inj cornerE_simple
    corner_cycles PW ψ hψ π hπ h1 h6

theorem corner_gauge_support_card {gauge : Representation k (Fin 7 → G) H}
    (PW : PeterWeylLattice k G cornerΓ Irr irr H gauge)
    (ψ : H) (hψ : ∀ g, gauge g ψ = ψ) (π : Fin cornerE.length → Irr) (hπ : PW.proj π ψ ≠ 0)
    (h1 : 1 ≤ (Finset.univ.filter (NTe (irr ∘ π))).card)
    (h6 : (Finset.univ.filter (NTe (irr ∘ π))).card ≤ 6) :
    (Finset.univ.filter (NTe (irr ∘ π))).card = 4 ∨
      (Finset.univ.filter (NTe (irr ∘ π))).card = 6 :=
  list_gauge_support_card cornerE 6 cornerΓ_links cornerΓ_norm_inj cornerE_simple
    corner_cycles PW ψ hψ π hπ h1 h6

theorem dcube_gauge_support_shortCycle {gauge : Representation k (Fin 12 → G) H}
    (PW : PeterWeylLattice k G dcubeΓ Irr irr H gauge)
    (ψ : H) (hψ : ∀ g, gauge g ψ = ψ) (π : Fin dcubeE.length → Irr) (hπ : PW.proj π ψ ≠ 0)
    (h1 : 1 ≤ (Finset.univ.filter (NTe (irr ∘ π))).card)
    (h6 : (Finset.univ.filter (NTe (irr ∘ π))).card ≤ 6) :
    shortCycle (supportList dcubeΓ (irr ∘ π) Fin.val) = true :=
  list_gauge_support_shortCycle dcubeE 11 dcubeΓ_links dcubeΓ_norm_inj dcubeE_simple
    dcube_cycles_of_codegree PW ψ hψ π hπ h1 h6

theorem dcube_gauge_support_card {gauge : Representation k (Fin 12 → G) H}
    (PW : PeterWeylLattice k G dcubeΓ Irr irr H gauge)
    (ψ : H) (hψ : ∀ g, gauge g ψ = ψ) (π : Fin dcubeE.length → Irr) (hπ : PW.proj π ψ ≠ 0)
    (h1 : 1 ≤ (Finset.univ.filter (NTe (irr ∘ π))).card)
    (h6 : (Finset.univ.filter (NTe (irr ∘ π))).card ≤ 6) :
    (Finset.univ.filter (NTe (irr ∘ π))).card = 4 ∨
      (Finset.univ.filter (NTe (irr ∘ π))).card = 6 :=
  list_gauge_support_card dcubeE 11 dcubeΓ_links dcubeΓ_norm_inj dcubeE_simple
    dcube_cycles_of_codegree PW ψ hψ π hπ h1 h6

/-- The double cube has no such support with exactly 5 non-trivial links. -/
theorem dcube_gauge_support_card_ne_five {gauge : Representation k (Fin 12 → G) H}
    (PW : PeterWeylLattice k G dcubeΓ Irr irr H gauge)
    (ψ : H) (hψ : ∀ g, gauge g ψ = ψ) (π : Fin dcubeE.length → Irr) (hπ : PW.proj π ψ ≠ 0) :
    (Finset.univ.filter (NTe (irr ∘ π))).card ≠ 5 := by
  intro h5
  have := dcube_gauge_support_card PW ψ hψ π hπ (by omega) (by omega)
  omega

end Instances

/-! ## The 5-link sublist used by the control -/

/-- A square `0-2-3-1` with a pendant link `3-7`: a 5-link sublist of `dcubeE`. -/
def dcubeFive : Graph := [(0, 2), (0, 1), (1, 3), (2, 3), (3, 7)]

theorem dcubeFive_sublist : dcubeFive.Sublist dcubeE := by decide

/-- It is not a short cycle (5 links, and vertex 7 has degree one). -/
theorem dcubeFive_not_shortCycle : shortCycle dcubeFive = false := by decide

end GraphInstances
