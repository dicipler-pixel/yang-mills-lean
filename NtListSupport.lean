import GaugeSupportRegroup
import SmallSupportBridge

/-!
# From the regrouped gauge support rule to the TailFloor support predicate

Author: Jeromie Beasley (Lean Green PR Machine, Grok Bot), with the Team.
ORCID https://orcid.org/0009-0006-4645-5643 · GitHub dicipler-pixel · X @d1c1pler ·
YouTube @AtlasMemoriae · atlas-memoriae.dicipler.workers.dev

`GaugeSupport.gauge_support_rule_regrouped` (Grey) says that, for a gauge-invariant state `ψ`
and a labelling `π` in its support, no vertex has exactly one non-trivial incident half-edge:
`ntList (incident Γ (irr ∘ π) v) ≠ [x]`. Here that rule is read as a TailFloor link list.

The non-trivial links of `π`, with vertices relabelled by an injective `lab : Vx → ℕ`, form
`supportList Γ π lab : TailFloor.Graph`. If no non-trivial link is a loop:
* `ntList_length_eq_deg`: the number of non-trivial half-edges at `v` is the list degree
  `TailFloor.deg (supportList Γ π lab) (lab v)`;
* `admissible_supportList`: the vertex rule makes the support `TailFloor.admissible`;
* `two_le_deg_of_admissible`: every touched vertex has degree at least 2;
* `gauge_support_admissible`: every labelling in the support of a gauge-invariant state gives
  an admissible list support (under Grey's named assumption `PeterWeylLattice`);
* `gauge_support_shortCycle`: if moreover its links lie in a host link list that is simple,
  two-coloured and of codegree at most 2 (`SmallSupportBridge`), and there are at most six
  of them, the support is a single connected 4- or 6-cycle (`TailFloor.shortCycle`).

Named hypothesis used: only Grey's `PeterWeylLattice` (Peter–Weyl link by link plus the
reshuffle into vertex blocks), a structure, not an axiom. The relabelling conditions
(`lab` injective, no non-trivial loop, no two non-trivial links with the same end pair) are
ordinary hypotheses. `K_{2,3}` is admissible but not a short cycle (`k23_admissible`,
`k23_not_shortCycle`), which is why the codegree condition is needed.

Scope: graph-theoretic Layer 3 fed by the gauge support rule, under the named Peter–Weyl
assumption.
-/

open CategoryTheory MonoidalCategory TailFloor GaugeSupport SmallSupportBridge
open scoped Classical

namespace NtListSupport

universe u v

theorem length_filter_toList {E : Type*} (A : Finset E) (b : E → Bool) :
    (A.toList.filter b).length = (A.filter (fun e => b e = true)).card := by
  rw [← List.toFinset_card_of_nodup ((Finset.nodup_toList A).filter _)]
  congr 1
  ext e
  simp

section Rep

variable {k : Type u} {G : Type v} [Field k] [Group G] {Vx E : Type*} [Fintype E]

/-- A link is non-trivial when its irrep is not the unit. -/
def NTe (π : E → FDRep k G) (e : E) : Prop := IsEmpty (𝟙_ (FDRep k G) ≅ π e)

/-- The non-trivial links of `π` as a TailFloor link list, vertices relabelled by `lab`. -/
noncomputable def supportList (Γ : OrientedGraph Vx E) (π : E → FDRep k G) (lab : Vx → ℕ) :
    Graph :=
  ((Finset.univ.filter (NTe π)).toList).map (fun e => (lab (Γ.src e), lab (Γ.tgt e)))

theorem ntList_length (Γ : OrientedGraph Vx E) (π : E → FDRep k G) (v : Vx) :
    (ntList (incident Γ π v)).length =
      (Finset.univ.filter (fun e => NTe π e ∧ Γ.src e = v)).card +
      (Finset.univ.filter (fun e => NTe π e ∧ Γ.tgt e = v)).card := by
  unfold ntList incident
  rw [List.filter_append, List.length_append, List.filter_map, List.filter_map,
    List.length_map, List.length_map, length_filter_toList, length_filter_toList,
    Finset.filter_filter, Finset.filter_filter]
  congr 2 <;>
  · apply Finset.filter_congr
    intro e _
    simp only [Function.comp_apply, NTe, HalfEdge.NT]
    exact ⟨fun ⟨a, b⟩ => ⟨of_decide_eq_true b, a⟩, fun ⟨a, b⟩ => ⟨b, decide_eq_true a⟩⟩

theorem deg_supportList (Γ : OrientedGraph Vx E) (π : E → FDRep k G) (lab : Vx → ℕ)
    (hlab : Function.Injective lab) (hloop : ∀ e, NTe π e → Γ.src e ≠ Γ.tgt e) (v : Vx) :
    deg (supportList Γ π lab) (lab v) =
      (Finset.univ.filter (fun e => NTe π e ∧ Γ.src e = v)).card +
      (Finset.univ.filter (fun e => NTe π e ∧ Γ.tgt e = v)).card := by
  unfold deg supportList
  rw [List.filter_map, List.length_map, length_filter_toList, Finset.filter_filter]
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext e
    simp only [Function.comp, Bool.or_eq_true, beq_iff_eq, hlab.eq_iff, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_union]
    tauto
  · rw [Finset.disjoint_left]
    intro e h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact hloop e h1.1 (h1.2.trans h2.2.symm)

/-- The non-trivial half-edges at `v` are counted by the list degree of the support. -/
theorem ntList_length_eq_deg (Γ : OrientedGraph Vx E) (π : E → FDRep k G) (lab : Vx → ℕ)
    (hlab : Function.Injective lab) (hloop : ∀ e, NTe π e → Γ.src e ≠ Γ.tgt e) (v : Vx) :
    (ntList (incident Γ π v)).length = deg (supportList Γ π lab) (lab v) := by
  rw [ntList_length, deg_supportList Γ π lab hlab hloop]

theorem mem_verts_supportList {Γ : OrientedGraph Vx E} {π : E → FDRep k G} {lab : Vx → ℕ}
    {w : ℕ} (hw : w ∈ verts (supportList Γ π lab)) : ∃ v, w = lab v := by
  obtain ⟨p, hp, h⟩ := (mem_verts _ _).1 hw
  simp only [supportList, List.mem_map] at hp
  obtain ⟨e, -, rfl⟩ := hp
  rcases h with h | h
  · exact ⟨Γ.src e, h.symm⟩
  · exact ⟨Γ.tgt e, h.symm⟩

/-- **The vertex rule makes the support admissible.** If no vertex has exactly one
non-trivial half-edge, the list support has no vertex of degree one. -/
theorem admissible_supportList (Γ : OrientedGraph Vx E) (π : E → FDRep k G) (lab : Vx → ℕ)
    (hlab : Function.Injective lab) (hloop : ∀ e, NTe π e → Γ.src e ≠ Γ.tgt e)
    (hrule : ∀ v, ∀ x, ntList (incident Γ π v) ≠ [x]) :
    admissible (supportList Γ π lab) = true := by
  unfold admissible
  rw [List.all_eq_true]
  intro w hw
  obtain ⟨v, rfl⟩ := mem_verts_supportList hw
  rw [← ntList_length_eq_deg Γ π lab hlab hloop v, bne_iff_ne, ne_eq, List.length_eq_one_iff]
  rintro ⟨x, hx⟩
  exact hrule v x hx

end Rep

/-- In an admissible support every touched vertex has degree at least 2. -/
theorem two_le_deg_of_admissible (s : Graph) (h : admissible s = true) {w : ℕ}
    (hw : w ∈ verts s) : 2 ≤ deg s w := by
  have h1 := List.all_eq_true.1 h w hw
  simp only [bne_iff_ne, ne_eq] at h1
  obtain ⟨e, he, hev⟩ := (mem_verts s w).1 hw
  have : 0 < deg s w := by
    unfold deg
    exact List.length_pos_of_mem (List.mem_filter.2 ⟨he, by simpa using hev⟩)
  omega

section Lattice

variable {k : Type u} {G : Type v} [Field k] [Group G] {Vx E : Type*} [Fintype E]

/-- **Gauge-invariant states have admissible supports.** Under the named Peter–Weyl
assumption, with every irrep simple: for a gauge-invariant `ψ` and a labelling `π` in its
support, the non-trivial links of `π`, read as a TailFloor link list, are admissible. -/
theorem gauge_support_admissible [DecidableEq Vx] {Γ : OrientedGraph Vx E} {Irr : Type*}
    {irr : Irr → FDRep k G} [∀ i, Simple (irr i)] {H : Type*} [AddCommGroup H] [Module k H]
    {gauge : Representation k (Vx → G) H} (PW : PeterWeylLattice k G Γ Irr irr H gauge)
    (ψ : H) (hψ : ∀ g, gauge g ψ = ψ) (π : E → Irr) (hπ : PW.proj π ψ ≠ 0)
    (lab : Vx → ℕ) (hlab : Function.Injective lab)
    (hloop : ∀ e, NTe (irr ∘ π) e → Γ.src e ≠ Γ.tgt e) :
    admissible (supportList Γ (irr ∘ π) lab) = true :=
  admissible_supportList Γ (irr ∘ π) lab hlab hloop
    (fun v => (gauge_support_rule_regrouped PW ψ hψ π hπ v).1)

/-- Every vertex touched by such a support has at least two non-trivial links. -/
theorem gauge_support_two_le_deg [DecidableEq Vx] {Γ : OrientedGraph Vx E} {Irr : Type*}
    {irr : Irr → FDRep k G} [∀ i, Simple (irr i)] {H : Type*} [AddCommGroup H] [Module k H]
    {gauge : Representation k (Vx → G) H} (PW : PeterWeylLattice k G Γ Irr irr H gauge)
    (ψ : H) (hψ : ∀ g, gauge g ψ = ψ) (π : E → Irr) (hπ : PW.proj π ψ ≠ 0)
    (lab : Vx → ℕ) (hlab : Function.Injective lab)
    (hloop : ∀ e, NTe (irr ∘ π) e → Γ.src e ≠ Γ.tgt e) {w : ℕ}
    (hw : w ∈ verts (supportList Γ (irr ∘ π) lab)) :
    2 ≤ deg (supportList Γ (irr ∘ π) lab) w :=
  two_le_deg_of_admissible _ (gauge_support_admissible PW ψ hψ π hπ lab hlab hloop) hw

/-- **Small gauge supports are 4- or 6-cycles.** Under the named Peter–Weyl assumption, with
every irrep simple: let `ψ` be gauge invariant and `π` in its support. Suppose the
non-trivial links of `π` (relabelled by an injective `lab`) lie in a host link list `g` that
is simple, two-coloured by `col` and of codegree at most 2. Suppose also that no two
non-trivial links share their end pair, and that there are between one and six of them.
Then they form a single connected 4- or 6-cycle. -/
theorem gauge_support_shortCycle [DecidableEq Vx] {Γ : OrientedGraph Vx E} {Irr : Type*}
    {irr : Irr → FDRep k G} [∀ i, Simple (irr i)] {H : Type*} [AddCommGroup H] [Module k H]
    {gauge : Representation k (Vx → G) H} (PW : PeterWeylLattice k G Γ Irr irr H gauge)
    (ψ : H) (hψ : ∀ g, gauge g ψ = ψ) (π : E → Irr) (hπ : PW.proj π ψ ≠ 0)
    (lab : Vx → ℕ) (hlab : Function.Injective lab)
    (hmulti : ∀ e e', NTe (irr ∘ π) e → NTe (irr ∘ π) e' →
      norm (lab (Γ.src e), lab (Γ.tgt e)) = norm (lab (Γ.src e'), lab (Γ.tgt e')) → e = e')
    (g : Graph) (col : ℕ → Bool) (hs : simpleB g = true) (hb : bipB col g = true)
    (hc : codeg2B g = true) (hsub : ∀ p ∈ supportList Γ (irr ∘ π) lab, p ∈ g)
    (hne : supportList Γ (irr ∘ π) lab ≠ []) (hlen : (supportList Γ (irr ∘ π) lab).length ≤ 6) :
    shortCycle (supportList Γ (irr ∘ π) lab) = true := by
  obtain ⟨gloop, -⟩ := simpleB_sound hs
  have hloop : ∀ e, NTe (irr ∘ π) e → Γ.src e ≠ Γ.tgt e := by
    intro e he h
    have hm : (lab (Γ.src e), lab (Γ.tgt e)) ∈ supportList Γ (irr ∘ π) lab := by
      simp only [supportList, List.mem_map, Finset.mem_toList, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact ⟨e, he, rfl⟩
    exact gloop _ (hsub _ hm) (by simp [h])
  have hadm := gauge_support_admissible PW ψ hψ π hπ lab hlab hloop
  set s := supportList Γ (irr ∘ π) lab with hsdef
  have hnd : (s.map norm).Nodup := by
    rw [hsdef, supportList, List.map_map]
    refine List.Nodup.map_on ?_ (Finset.nodup_toList _)
    intro e he e' he' h
    simp only [Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] at he he'
    exact hmulti e e' he he' h
  have hadj : ∀ u w, adjP s u w → adjP g u w := fun u w h => h.imp (hsub _) (hsub _)
  have hcod := codeg2B_sound hc
  have hbip := bipB_sound hb
  exact shortCycle_of s col (fun e he => gloop e (hsub e he)) hnd (fun e he => hbip e (hsub e he))
    (fun u w huw T hT => hcod u w huw T (fun x hx => ⟨hadj _ _ (hT x hx).1, hadj _ _ (hT x hx).2⟩))
    hne hlen hadm

end Lattice

/-! ## `K_{2,3}`: admissible, not a short cycle -/

/-- `K_{2,3}` passes the vertex rule's degree test (no vertex of degree one). -/
theorem k23_admissible : admissible k23E = true := by decide

/-- …but it is not a 4- or 6-cycle; on a codegree-≤2 host it cannot occur
(`SmallSupportBridge.k23_codegree_fails`). -/
theorem k23_not_shortCycle : shortCycle k23E = false := by decide

end NtListSupport
