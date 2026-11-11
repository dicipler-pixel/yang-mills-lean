import NtListSupport

/-!
# List order does not matter, and the cube instance

Author: Jeromie Beasley (Lean Green PR Machine, Grok Bot), with the Team.
ORCID https://orcid.org/0009-0006-4645-5643 · GitHub dicipler-pixel · X @d1c1pler ·
YouTube @AtlasMemoriae · atlas-memoriae.dicipler.workers.dev

`NtListSupport.supportList` lists the non-trivial links in `Finset.toList` order, while
`TailFloor.smallSupports g` enumerates ordered sublists of the host `g`. This file closes that
gap and applies the result to the cube.

**Order invariance.** For `s ~ t` (`List.Perm`):
* `deg_perm`, `mem_verts_perm`, `admissible_perm`: degree, vertex membership and
  admissibility are unchanged;
* `reach_sound`, `connected_sound`: every vertex `reach` collects is linked to the start by
  links of the list, so `connected s = true` makes any two vertices linked;
* `connected_of_perm`, `shortCycle_of_perm`: for a target list with no loops and no repeated
  link, `connected` and `shortCycle` transfer along a permutation.

**Landing in `SmallSupportsAreCycles`.**
* `mem_smallSupports_of_sublist`: every sublist of `g` with 1 to 6 links is enumerated by
  `smallSupports g`.
* `filter_perm`: for nodup `s ⊆ g` and nodup `g`, `g.filter (· ∈ s)` is a sublist of `g` and a
  permutation of `s` (same links, same orientation).
* `gauge_support_shortCycle_of_SSAC`: if the host satisfies `SmallSupportsAreCycles g`, then
  every gauge support (under the named `PeterWeylLattice`) with 1 to 6 links inside `g` is a
  4- or 6-cycle. Its reordering `g.filter (· ∈ s)` is one of the supports the predicate
  quantifies over. No colouring or codegree hypothesis is needed here, only the predicate.

**Cube.** `cubeΓ : OrientedGraph (Fin 8) (Fin 12)` has link `i` oriented as the `i`-th pair
of `TailFloor.cubeE`, and `lab = Fin.val`. `cube_gauge_support_shortCycle`: under
`PeterWeylLattice` alone (every irrep simple), every labelling in the support of a
gauge-invariant state with 1 to 6 non-trivial links has those links forming a single
connected 4- or 6-cycle. The host predicate is `TailFloor.cube_cycles`.

Named hypothesis: only Grey's `PeterWeylLattice` (a structure, not an axiom).
-/

open CategoryTheory TailFloor GaugeSupport SmallSupportBridge NtListSupport
open scoped Classical

namespace PermCube

universe u v

/-! ## Order invariance -/

theorem deg_perm {s t : Graph} (h : s.Perm t) (v : ℕ) : deg s v = deg t v :=
  (h.filter _).length_eq

theorem mem_verts_perm {s t : Graph} (h : s.Perm t) (v : ℕ) : v ∈ verts s ↔ v ∈ verts t := by
  rw [mem_verts, mem_verts]
  exact ⟨fun ⟨e, he, h'⟩ => ⟨e, h.subset he, h'⟩, fun ⟨e, he, h'⟩ => ⟨e, h.symm.subset he, h'⟩⟩

theorem admissible_perm {s t : Graph} (h : s.Perm t) : admissible s = admissible t := by
  rw [Bool.eq_iff_iff]
  unfold admissible
  simp only [List.all_eq_true]
  constructor
  · intro hs v hv
    rw [← deg_perm h]; exact hs v ((mem_verts_perm h v).2 hv)
  · intro ht v hv
    rw [deg_perm h]; exact ht v ((mem_verts_perm h v).1 hv)

theorem adjP_perm {s t : Graph} (h : s.Perm t) (a b : ℕ) : adjP s a b ↔ adjP t a b := by
  unfold adjP; rw [h.mem_iff, h.mem_iff]

theorem pass_sound (s : Graph) : ∀ (l : Graph), l ⊆ s → ∀ (acc : List ℕ) (x : ℕ),
    x ∈ SmallSupportBridge.pass l acc → ∃ y ∈ acc, Relation.ReflTransGen (adjP s) y x := by
  intro l
  induction l with
  | nil => intro _ acc x hx; exact ⟨x, hx, Relation.ReflTransGen.refl⟩
  | cons e es ih =>
    intro hl acc x hx
    have he : e ∈ s := hl (List.mem_cons_self)
    obtain ⟨y, hy, hyx⟩ := ih (fun a ha => hl (List.mem_cons_of_mem _ ha)) _ x hx
    simp only at hy
    split_ifs at hy with h1 h2
    · simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem] at h1
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ⟨e.1, h1.1, Relation.ReflTransGen.head (Or.inl he) hyx⟩
      · exact ⟨y, hy, hyx⟩
    · simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem] at h2
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ⟨e.2, h2.1, Relation.ReflTransGen.head (Or.inr he) hyx⟩
      · exact ⟨y, hy, hyx⟩
    · exact ⟨y, hy, hyx⟩

theorem reach_sound (s : Graph) : ∀ (n : ℕ) (acc : List ℕ) (x : ℕ),
    x ∈ reach s n acc → ∃ y ∈ acc, Relation.ReflTransGen (adjP s) y x
  | 0, _, x, hx => ⟨x, hx, Relation.ReflTransGen.refl⟩
  | n + 1, acc, x, hx => by
    rw [reach_succ] at hx
    obtain ⟨y, hy, hyx⟩ := reach_sound s n _ x hx
    obtain ⟨z, hz, hzy⟩ := pass_sound s s (fun _ h => h) acc y hy
    exact ⟨z, hz, hzy.trans hyx⟩

theorem rtg_symm {s : Graph} {a b : ℕ} (h : Relation.ReflTransGen (adjP s) a b) :
    Relation.ReflTransGen (adjP s) b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (Or.symm hbc) ih

/-- `connected s = true` links any two vertices of `s` by links of `s`. -/
theorem connected_sound {s : Graph} (h : connected s = true) {u w : ℕ} (hu : u ∈ verts s)
    (hw : w ∈ verts s) : Relation.ReflTransGen (adjP s) u w := by
  unfold connected at h
  split at h
  · next hv => rw [hv] at hu; simp at hu
  · next v rest hv =>
    have root : ∀ x ∈ verts s, Relation.ReflTransGen (adjP s) v x := by
      intro x hx
      have := List.all_eq_true.1 h x hx
      rw [List.contains_iff_mem] at this
      obtain ⟨y, hy, hyx⟩ := reach_sound s _ _ x this
      simp only [List.mem_singleton] at hy
      exact hy ▸ hyx
    exact (rtg_symm (root u hu)).trans (root w hw)

theorem reachable_of_rtg {s : Graph} {a b : ℕ} (h : Relation.ReflTransGen (adjP s) a b)
    (ha : a ∈ (verts s).toFinset) (hb : b ∈ (verts s).toFinset) :
    (supG s).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail c d hac hcd ih =>
    have hc : c ∈ (verts s).toFinset := List.mem_toFinset.2 (adjP_verts hcd).1
    refine (ih hc).trans ?_
    by_cases hcd' : c = d
    · subst hcd'; exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable (supG_adj.2 ⟨hcd', hcd⟩)

/-- `connected` transfers along a permutation onto a list with no loops and no repeated link. -/
theorem connected_of_perm {s t : Graph} (hp : t.Perm s) (hloop : ∀ e ∈ s, e.1 ≠ e.2)
    (hnd : (s.map norm).Nodup) (hne : s ≠ []) (h : connected t = true) : connected s = true := by
  apply connected_of_connected hloop hnd
  obtain ⟨e0, he0⟩ := List.exists_mem_of_ne_nil s hne
  have : Nonempty (Sup s) := ⟨⟨e0.1, mem_sup.2 ⟨e0, he0, Or.inl rfl⟩⟩⟩
  refine SimpleGraph.Connected.mk (fun u w => ?_)
  have hu : u.1 ∈ verts t := (mem_verts_perm hp _).2 (List.mem_toFinset.1 u.2)
  have hw : w.1 ∈ verts t := (mem_verts_perm hp _).2 (List.mem_toFinset.1 w.2)
  have h1 := connected_sound h hu hw
  have h2 : Relation.ReflTransGen (adjP s) u.1 w.1 :=
    Relation.ReflTransGen.mono (fun a b hab => (adjP_perm hp a b).1 hab) _ _ h1
  exact reachable_of_rtg h2 u.2 w.2

/-- `shortCycle` transfers along a permutation onto a list with no loops and no repeated link. -/
theorem shortCycle_of_perm {s t : Graph} (hp : t.Perm s) (hloop : ∀ e ∈ s, e.1 ≠ e.2)
    (hnd : (s.map norm).Nodup) (h : shortCycle t = true) : shortCycle s = true := by
  unfold shortCycle at h ⊢
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true] at h ⊢
  obtain ⟨⟨hl, hd⟩, hc⟩ := h
  have hlen := hp.length_eq
  have hne : s ≠ [] := by
    rintro rfl
    simp only [List.length_nil] at hlen
    omega
  refine ⟨⟨by omega, fun v hv => ?_⟩, connected_of_perm hp hloop hnd hne hc⟩
  rw [← deg_perm hp]
  exact hd v ((mem_verts_perm hp v).2 hv)

/-! ## Sublists of the host are enumerated by `smallSupports` -/

theorem mem_choose_of_sublist : ∀ {t l : Graph}, t.Sublist l → t ∈ TailFloor.choose t.length l
  | _, _, .slnil => by simp [TailFloor.choose]
  | t, _ :: l, .cons a h => by
    rcases t with _ | ⟨b, t⟩
    · cases l <;> simp [TailFloor.choose]
    · simp only [List.length_cons, TailFloor.choose, List.mem_append]
      exact Or.inr (by simpa using mem_choose_of_sublist h)
  | _ :: t, _ :: l, .cons_cons a h => by
    simp only [List.length_cons, TailFloor.choose, List.mem_append, List.mem_map]
    exact Or.inl ⟨t, mem_choose_of_sublist h, rfl⟩

theorem mem_smallSupports_of_sublist {t g : Graph} (h : t.Sublist g) (hne : t ≠ [])
    (h6 : t.length ≤ 6) : t ∈ smallSupports g := by
  simp only [smallSupports, List.mem_flatMap, List.mem_range]
  have hpos : 0 < t.length := List.length_pos_iff.2 hne
  refine ⟨t.length - 1, by omega, ?_⟩
  have := mem_choose_of_sublist h
  rwa [show t.length = t.length - 1 + 1 by omega] at this

/-- The host's own ordering of a support: same links, same orientation. -/
theorem filter_perm {s g : Graph} (hs : s.Nodup) (hg : g.Nodup) (hsub : ∀ p ∈ s, p ∈ g) :
    (g.filter (fun p => decide (p ∈ s))).Sublist g ∧ (g.filter (fun p => decide (p ∈ s))).Perm s := by
  refine ⟨List.filter_sublist, ?_⟩
  rw [List.perm_ext_iff_of_nodup (hg.filter _) hs]
  intro p
  simp only [List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨hsub p h, h⟩⟩

/-! ## Gauge supports land in `SmallSupportsAreCycles` -/

section Lattice

variable {k : Type u} {G : Type v} [Field k] [Group G] {Vx E : Type*} [Fintype E]

theorem supportList_nodup_norm {Γ : OrientedGraph Vx E} {π : E → FDRep k G} {lab : Vx → ℕ}
    (hmulti : ∀ e e', NTe π e → NTe π e' →
      norm (lab (Γ.src e), lab (Γ.tgt e)) = norm (lab (Γ.src e'), lab (Γ.tgt e')) → e = e') :
    ((supportList Γ π lab).map norm).Nodup := by
  rw [supportList, List.map_map]
  refine List.Nodup.map_on ?_ (Finset.nodup_toList _)
  intro e he e' he' h
  simp only [Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] at he he'
  exact hmulti e e' he he' h

/-- **Gauge supports from the host predicate.** Under the named Peter–Weyl assumption, with
every irrep simple: let `ψ` be gauge invariant and `π` in its support. Suppose the
non-trivial links of `π` (relabelled by an injective `lab`, no two sharing an end pair) lie,
with their orientation, in a host `g` with no loops and no repeated link. If there are 1 to
6 of them and `SmallSupportsAreCycles g` holds, they form a single connected 4- or 6-cycle.
Their reordering `g.filter (· ∈ supportList)` is a support the predicate covers. -/
theorem gauge_support_shortCycle_of_SSAC [DecidableEq Vx] {Γ : OrientedGraph Vx E} {Irr : Type*}
    {irr : Irr → FDRep k G} [∀ i, Simple (irr i)] {H : Type*} [AddCommGroup H] [Module k H]
    {gauge : Representation k (Vx → G) H} (PW : PeterWeylLattice k G Γ Irr irr H gauge)
    (ψ : H) (hψ : ∀ g, gauge g ψ = ψ) (π : E → Irr) (hπ : PW.proj π ψ ≠ 0)
    (lab : Vx → ℕ) (hlab : Function.Injective lab)
    (hmulti : ∀ e e', NTe (irr ∘ π) e → NTe (irr ∘ π) e' →
      norm (lab (Γ.src e), lab (Γ.tgt e)) = norm (lab (Γ.src e'), lab (Γ.tgt e')) → e = e')
    (g : Graph) (hg : simpleB g = true) (hSSAC : SmallSupportsAreCycles g)
    (hsub : ∀ p ∈ supportList Γ (irr ∘ π) lab, p ∈ g)
    (hne : supportList Γ (irr ∘ π) lab ≠ []) (hlen : (supportList Γ (irr ∘ π) lab).length ≤ 6) :
    shortCycle (supportList Γ (irr ∘ π) lab) = true := by
  obtain ⟨gloop, gnd⟩ := simpleB_sound hg
  set s := supportList Γ (irr ∘ π) lab with hsdef
  have hloop : ∀ e, NTe (irr ∘ π) e → Γ.src e ≠ Γ.tgt e := by
    intro e he h
    have hm : (lab (Γ.src e), lab (Γ.tgt e)) ∈ s := by
      simp only [hsdef, supportList, List.mem_map, Finset.mem_toList, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact ⟨e, he, rfl⟩
    exact gloop _ (hsub _ hm) (by simp [h])
  have hadm : admissible s = true := gauge_support_admissible PW ψ hψ π hπ lab hlab hloop
  have hnd : (s.map norm).Nodup := supportList_nodup_norm hmulti
  obtain ⟨hsl, hperm⟩ := filter_perm (hnd.of_map _) (gnd.of_map _) hsub
  set t := g.filter (fun p => decide (p ∈ s))
  have htne : t ≠ [] := by
    intro h; apply hne; rw [h] at hperm; exact hperm.symm.eq_nil
  have hmem : t ∈ smallSupports g :=
    mem_smallSupports_of_sublist hsl htne (by rw [hperm.length_eq]; exact hlen)
  have htc : shortCycle t = true := hSSAC t hmem (by rw [admissible_perm hperm]; exact hadm)
  exact shortCycle_of_perm hperm (fun e he => gloop e (hsub e he)) hnd htc

end Lattice

/-! ## The cube -/

/-- Endpoint `j` of link `i` of `TailFloor.cubeE`, as a vertex of `Fin 8`. -/
def cubeEnd (i : Fin 12) (first : Bool) : Fin 8 :=
  ⟨(if first then (cubeE.getD i (0, 0)).1 else (cubeE.getD i (0, 0)).2) % 8,
    Nat.mod_lt _ (by decide)⟩

/-- The cube as an oriented graph: link `i` runs as the `i`-th pair of `TailFloor.cubeE`. -/
def cubeΓ : OrientedGraph (Fin 8) (Fin 12) where
  src i := cubeEnd i true
  tgt i := cubeEnd i false

theorem cubeΓ_link_mem : ∀ i : Fin 12, ((cubeΓ.src i).val, (cubeΓ.tgt i).val) ∈ cubeE := by
  decide

theorem cubeΓ_norm_inj : ∀ i j : Fin 12,
    norm ((cubeΓ.src i).val, (cubeΓ.tgt i).val) = norm ((cubeΓ.src j).val, (cubeΓ.tgt j).val) →
      i = j := by
  decide

theorem cubeE_simple : simpleB cubeE = true := by decide

theorem supportList_length {Vx E : Type*} [Fintype E] {k : Type u} {G : Type v} [Field k]
    [Group G] (Γ : OrientedGraph Vx E) (π : E → FDRep k G) (lab : Vx → ℕ) :
    (supportList Γ π lab).length = (Finset.univ.filter (NTe π)).card := by
  simp [supportList]

/-- **The cube.** Under the named Peter–Weyl assumption alone (every irrep simple): for a
gauge-invariant state `ψ` and any labelling `π` of the 12 cube links in its support with
between 1 and 6 non-trivial links, those links form a single connected 4- or 6-cycle. -/
theorem cube_gauge_support_shortCycle {k : Type u} {G : Type v} [Field k] [Group G]
    {Irr : Type*} {irr : Irr → FDRep k G} [∀ i, Simple (irr i)] {H : Type*} [AddCommGroup H]
    [Module k H] {gauge : Representation k (Fin 8 → G) H}
    (PW : PeterWeylLattice k G cubeΓ Irr irr H gauge)
    (ψ : H) (hψ : ∀ g, gauge g ψ = ψ) (π : Fin 12 → Irr) (hπ : PW.proj π ψ ≠ 0)
    (h1 : 1 ≤ (Finset.univ.filter (NTe (irr ∘ π))).card)
    (h6 : (Finset.univ.filter (NTe (irr ∘ π))).card ≤ 6) :
    shortCycle (supportList cubeΓ (irr ∘ π) Fin.val) = true := by
  have hlen := supportList_length cubeΓ (irr ∘ π) Fin.val
  refine gauge_support_shortCycle_of_SSAC PW ψ hψ π hπ Fin.val Fin.val_injective
    (fun e e' _ _ h => cubeΓ_norm_inj e e' h) cubeE cubeE_simple cube_cycles ?_ ?_ (by omega)
  · intro p hp
    simp only [supportList, List.mem_map] at hp
    obtain ⟨e, -, rfl⟩ := hp
    exact cubeΓ_link_mem e
  · intro h; rw [h] at hlen; simp at hlen; omega

/-- On the cube such a support has exactly 4 or 6 links. -/
theorem cube_gauge_support_card {k : Type u} {G : Type v} [Field k] [Group G]
    {Irr : Type*} {irr : Irr → FDRep k G} [∀ i, Simple (irr i)] {H : Type*} [AddCommGroup H]
    [Module k H] {gauge : Representation k (Fin 8 → G) H}
    (PW : PeterWeylLattice k G cubeΓ Irr irr H gauge)
    (ψ : H) (hψ : ∀ g, gauge g ψ = ψ) (π : Fin 12 → Irr) (hπ : PW.proj π ψ ≠ 0)
    (h1 : 1 ≤ (Finset.univ.filter (NTe (irr ∘ π))).card)
    (h6 : (Finset.univ.filter (NTe (irr ∘ π))).card ≤ 6) :
    (Finset.univ.filter (NTe (irr ∘ π))).card = 4 ∨
      (Finset.univ.filter (NTe (irr ∘ π))).card = 6 := by
  have h := cube_gauge_support_shortCycle PW ψ hψ π hπ h1 h6
  rw [← supportList_length cubeΓ (irr ∘ π) Fin.val]
  unfold shortCycle at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact h.1.1

/-! ## Checks -/

/-- Reordering a support does not change a degree. -/
theorem deg_reorder_example : deg [(0, 1), (1, 2), (2, 3), (3, 0)] 1 = deg [(3, 0), (2, 3), (1, 2), (0, 1)] 1 :=
  deg_perm (by decide) 1

end PermCube
