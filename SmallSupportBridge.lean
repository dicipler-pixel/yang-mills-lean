import SmallSupportCycle
import TailFloor

/-!
# Small support bridge: list supports to `SimpleGraph`, general Layer 3

Author: Jeromie Beasley (Lean Green PR Machine, Grok Bot), with the Team.
ORCID https://orcid.org/0009-0006-4645-5643 · GitHub dicipler-pixel · X @d1c1pler ·
YouTube @AtlasMemoriae · atlas-memoriae.dicipler.workers.dev

This file closes the open item of `SmallSupportCycle.lean`: it connects the general
`SimpleGraph` statement `StructuralSupport.small_support_is_cycle` to the list-based
`TailFloor.SmallSupportsAreCycles` used in `TailFloor.lean`.

A link support `s : TailFloor.Graph` is relabelled as the simple graph `supG s` on its own
vertex set `verts s`. Under "no loops, no repeated link" we prove

* `degree_eq_deg`: the list degree `TailFloor.deg` is the `SimpleGraph` degree;
* `card_edgeFinset_eq_length`: the number of links is the `SimpleGraph` edge count;
* `connected_of_connected`: a connected `supG s` makes the list checker `TailFloor.connected`
  return `true` (a shortest path has at most `s.length` links, and each `reach` pass extends
  the reached set across every link).

Main result, `smallSupportsAreCycles_of`: on any host link list that is simple, has a
two-colouring, and in which two distinct vertices share at most two neighbours,
`TailFloor.SmallSupportsAreCycles` holds. `smallSupportsAreCycles_of_check` is the same with
the three host conditions as cheap Boolean checks, so the five test graphs (including the
20-link double cube) follow by checking only a colouring and the codegree, without
enumerating supports. The existing search-based theorems are untouched. `K_{2,3}` has three
common neighbours for its two hubs, so it fails the codegree check (`k23_codegree_fails`),
consistent with the false control `TailFloor.k23_control`.

Scope: this is the graph-theoretic Layer 3 only. Layer 2 (the gauge support rule) stays open.
-/

open Finset TailFloor

namespace SmallSupportBridge

/-! ## Host conditions -/

/-- a link as an unordered pair -/
def norm (e : ℕ × ℕ) : ℕ × ℕ := (min e.1 e.2, max e.1 e.2)

/-- adjacency in a link list, either orientation -/
def adjP (s : Graph) (u w : ℕ) : Prop := (u, w) ∈ s ∨ (w, u) ∈ s

/-- Boolean adjacency in a link list -/
def adjB (s : Graph) (u w : ℕ) : Bool :=
  s.any (fun e => (e.1 == u && e.2 == w) || (e.1 == w && e.2 == u))

/-- no loops and no link repeated in either orientation -/
def simpleB (g : Graph) : Bool := g.all (fun e => e.1 != e.2) && decide (g.map norm).Nodup

/-- `col` is a proper two-colouring of the links -/
def bipB (col : ℕ → Bool) (g : Graph) : Bool := g.all (fun e => col e.1 != col e.2)

/-- any two distinct vertices have at most two common neighbours -/
def codeg2B (g : Graph) : Bool :=
  (verts g).all fun u => (verts g).all fun v =>
    u == v || decide (((verts g).filter (fun w => adjB g u w && adjB g v w)).length ≤ 2)

theorem mem_verts (s : Graph) (v : ℕ) : v ∈ verts s ↔ ∃ e ∈ s, e.1 = v ∨ e.2 = v := by
  simp only [verts, List.mem_eraseDups, List.mem_append, List.mem_map]
  constructor
  · rintro (⟨e, he, h⟩ | ⟨e, he, h⟩)
    · exact ⟨e, he, Or.inl h⟩
    · exact ⟨e, he, Or.inr h⟩
  · rintro ⟨e, he, h | h⟩
    · exact Or.inl ⟨e, he, h⟩
    · exact Or.inr ⟨e, he, h⟩

theorem adjB_iff (s : Graph) (u w : ℕ) : adjB s u w = true ↔ adjP s u w := by
  simp only [adjB, adjP, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨a, b⟩, he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact Or.inl he
    · exact Or.inr he
  · rintro (h | h)
    · exact ⟨_, h, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨_, h, Or.inr ⟨rfl, rfl⟩⟩

theorem adjP_verts {s : Graph} {u w : ℕ} (h : adjP s u w) : u ∈ verts s ∧ w ∈ verts s := by
  rcases h with h | h
  · exact ⟨(mem_verts _ _).2 ⟨_, h, Or.inl rfl⟩, (mem_verts _ _).2 ⟨_, h, Or.inr rfl⟩⟩
  · exact ⟨(mem_verts _ _).2 ⟨_, h, Or.inr rfl⟩, (mem_verts _ _).2 ⟨_, h, Or.inl rfl⟩⟩

theorem simpleB_sound {g : Graph} (h : simpleB g = true) :
    (∀ e ∈ g, e.1 ≠ e.2) ∧ (g.map norm).Nodup := by
  simpa [simpleB] using h

theorem bipB_sound {col : ℕ → Bool} {g : Graph} (h : bipB col g = true) :
    ∀ e ∈ g, col e.1 ≠ col e.2 := by
  simpa [bipB] using h

theorem codeg2B_sound {g : Graph} (h : codeg2B g = true) :
    ∀ u v, u ≠ v → ∀ T : Finset ℕ, (∀ w ∈ T, adjP g u w ∧ adjP g v w) → #T ≤ 2 := by
  intro u v huv T hT
  rcases T.eq_empty_or_nonempty with rfl | ⟨w0, hw0⟩
  · simp
  have hu := (adjP_verts (hT w0 hw0).1).1
  have hv := (adjP_verts (hT w0 hw0).2).1
  have h2 := List.all_eq_true.1 (List.all_eq_true.1 h u hu) v hv
  simp only [Bool.or_eq_true, beq_iff_eq, huv, false_or, decide_eq_true_eq] at h2
  refine le_trans ?_ (le_trans (List.toFinset_card_le _) h2)
  apply Finset.card_le_card
  intro w hw
  simp only [List.mem_toFinset, List.mem_filter, Bool.and_eq_true, adjB_iff]
  exact ⟨(adjP_verts (hT w hw).1).2, hT w hw⟩

/-! ## The relabelled simple graph of a support -/

/-- the vertices of a support -/
abbrev Sup (s : Graph) := {v : ℕ // v ∈ (verts s).toFinset}

/-- a support as a simple graph on its own vertices -/
def supG (s : Graph) : SimpleGraph (Sup s) := SimpleGraph.fromRel (fun u w => (u.1, w.1) ∈ s)

instance (s : Graph) : DecidableRel (supG s).Adj := fun u w =>
  decidable_of_iff _ (SimpleGraph.fromRel_adj (fun u w : Sup s => (u.1, w.1) ∈ s) u w).symm

theorem supG_adj {s : Graph} {u w : Sup s} : (supG s).Adj u w ↔ u.1 ≠ w.1 ∧ adjP s u.1 w.1 := by
  unfold supG
  rw [SimpleGraph.fromRel_adj]
  simp only [adjP, ne_eq, Subtype.ext_iff]

theorem mem_sup {s : Graph} {v : ℕ} : v ∈ (verts s).toFinset ↔ ∃ e ∈ s, e.1 = v ∨ e.2 = v := by
  rw [List.mem_toFinset, mem_verts]

/-- the other end of a link at `v` -/
def other (v : ℕ) (e : ℕ × ℕ) : ℕ := if e.1 = v then e.2 else e.1

/-- the list degree is the `SimpleGraph` degree -/
theorem degree_eq_deg {s : Graph} (hloop : ∀ e ∈ s, e.1 ≠ e.2) (hnd : (s.map norm).Nodup)
    (v : Sup s) : (supG s).degree v = deg s v.1 := by
  set L := (s.filter (fun e => e.1 == v.1 || e.2 == v.1)).map (other v.1) with hL
  have hsnd : s.Nodup := hnd.of_map _
  have hLnd : L.Nodup := by
    refine List.Nodup.map_on ?_ (hsnd.filter _)
    intro x hx y hy hxy
    simp only [List.mem_filter, Bool.or_eq_true, beq_iff_eq] at hx hy
    apply List.inj_on_of_nodup_map hnd hx.1 hy.1
    have h1 := hloop x hx.1; have h2 := hloop y hy.1
    obtain ⟨a, b⟩ := x; obtain ⟨c, d⟩ := y
    simp only [other, norm, Prod.ext_iff] at hxy h1 h2 hx hy ⊢
    split_ifs at hxy <;> omega
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← Finset.card_map (Function.Embedding.subtype _), deg]
  have : ((supG s).neighborFinset v).map (Function.Embedding.subtype _) = L.toFinset := by
    ext w
    simp only [Finset.mem_map, SimpleGraph.mem_neighborFinset, supG_adj,
      Function.Embedding.coe_subtype, List.mem_toFinset, hL, List.mem_map, List.mem_filter,
      Bool.or_eq_true, beq_iff_eq, adjP]
    constructor
    · rintro ⟨x, ⟨hne, h | h⟩, rfl⟩
      · exact ⟨_, ⟨h, Or.inl rfl⟩, by simp [other]⟩
      · exact ⟨_, ⟨h, Or.inr rfl⟩, by simp [other, Ne.symm hne]⟩
    · rintro ⟨e, ⟨he, h⟩, rfl⟩
      have hl := hloop e he
      by_cases h1 : e.1 = v.1
      · refine ⟨⟨e.2, mem_sup.2 ⟨e, he, Or.inr rfl⟩⟩, ⟨by simp; omega, Or.inl ?_⟩, by simp [other, h1]⟩
        rw [← h1]; exact he
      · have h2 : e.2 = v.1 := h.resolve_left h1
        refine ⟨⟨e.1, mem_sup.2 ⟨e, he, Or.inl rfl⟩⟩, ⟨by simp; omega, Or.inr ?_⟩, by simp [other, h1]⟩
        rw [← h2]; exact he
  rw [this, List.toFinset_card_of_nodup hLnd, hL, List.length_map]

/-- the number of links is the `SimpleGraph` edge count -/
theorem card_edgeFinset_eq_length {s : Graph} (hloop : ∀ e ∈ s, e.1 ≠ e.2)
    (hnd : (s.map norm).Nodup) : #(supG s).edgeFinset = s.length := by
  have hsym : (s.map (fun e => s(e.1, e.2))).Nodup := by
    refine List.Nodup.map_on ?_ (hnd.of_map _)
    intro x hx y hy hxy
    apply List.inj_on_of_nodup_map hnd hx hy
    obtain ⟨a, b⟩ := x; obtain ⟨c, d⟩ := y
    simp only [Sym2.eq_iff, norm, Prod.ext_iff] at *
    omega
  let f : Sym2 (Sup s) ↪ Sym2 ℕ := ⟨Sym2.map Subtype.val, Sym2.map.injective Subtype.val_injective⟩
  have : (supG s).edgeFinset.map f = (s.map (fun e => s(e.1, e.2))).toFinset := by
    ext z
    simp only [Finset.mem_map, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨e', he', rfl⟩
      induction e' using Sym2.ind with
      | h x y =>
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, supG_adj] at he'
        rcases he'.2 with h | h
        · exact ⟨_, h, by simp [f]⟩
        · exact ⟨_, h, by simp [f, Sym2.eq_swap]⟩
    · rintro ⟨e, he, rfl⟩
      refine ⟨s(⟨e.1, mem_sup.2 ⟨e, he, Or.inl rfl⟩⟩, ⟨e.2, mem_sup.2 ⟨e, he, Or.inr rfl⟩⟩), ?_,
        by simp [f]⟩
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, supG_adj]
      exact ⟨hloop e he, Or.inl he⟩
  rw [← Finset.card_map f, this, List.toFinset_card_of_nodup hsym, List.length_map]

/-! ## Connectivity: the list checker `reach` -/

/-- one `reach` pass, as in `TailFloor.reach` -/
def pass (s : Graph) (acc : List ℕ) : List ℕ := s.foldl (fun a e =>
  if a.contains e.1 && !a.contains e.2 then e.2 :: a
  else if a.contains e.2 && !a.contains e.1 then e.1 :: a else a) acc

theorem reach_succ (s : Graph) (n : ℕ) (acc : List ℕ) :
    reach s (n + 1) acc = reach s n (pass s acc) := rfl

theorem foldl_mono (l : Graph) {x : ℕ} : ∀ acc : List ℕ, x ∈ acc → x ∈ pass l acc := by
  induction l with
  | nil => intro acc h; exact h
  | cons e es ih =>
    intro acc h
    apply ih
    simp only
    split_ifs <;> simp [h]

theorem foldl_edge (l : Graph) {e : ℕ × ℕ} (he : e ∈ l) :
    ∀ acc : List ℕ, (e.1 ∈ acc ∨ e.2 ∈ acc) → e.2 ∈ pass l acc ∧ e.1 ∈ pass l acc := by
  induction l with
  | nil => simp at he
  | cons e' es ih =>
    intro acc h
    rcases List.mem_cons.1 he with rfl | he'
    · have hb : e.1 ∈ (fun a (e : ℕ × ℕ) => if a.contains e.1 && !a.contains e.2 then e.2 :: a
          else if a.contains e.2 && !a.contains e.1 then e.1 :: a else a) acc e ∧
          e.2 ∈ (fun a (e : ℕ × ℕ) => if a.contains e.1 && !a.contains e.2 then e.2 :: a
          else if a.contains e.2 && !a.contains e.1 then e.1 :: a else a) acc e := by
        by_cases h1 : e.1 ∈ acc <;> by_cases h2 : e.2 ∈ acc <;> simp_all
      exact ⟨foldl_mono es _ hb.2, foldl_mono es _ hb.1⟩
    · exact ih he' _ (by
        rcases h with h | h
        · exact Or.inl (by simp only; split_ifs <;> simp [h])
        · exact Or.inr (by simp only; split_ifs <;> simp [h]))

theorem reach_mono (s : Graph) {x : ℕ} : ∀ (n : ℕ) (acc : List ℕ), x ∈ acc → x ∈ reach s n acc
  | 0, _, h => h
  | n + 1, acc, h => by rw [reach_succ]; exact reach_mono s n _ (foldl_mono s acc h)

theorem walk_reach {s : Graph} {x y : Sup s} (p : (supG s).Walk x y) :
    ∀ (n : ℕ) (acc : List ℕ), p.length ≤ n → x.1 ∈ acc → y.1 ∈ reach s n acc := by
  induction p with
  | nil => intro n acc _ h; exact reach_mono s n acc h
  | @cons a b c hab p ih =>
    intro n acc hn ha
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    rw [reach_succ]
    apply ih m _ (by simp at hn; omega)
    rcases (supG_adj.1 hab).2 with h | h
    · exact (foldl_edge s h acc (Or.inl ha)).1
    · exact (foldl_edge s h acc (Or.inr ha)).2

theorem connected_of_connected {s : Graph} (hloop : ∀ e ∈ s, e.1 ≠ e.2)
    (hnd : (s.map norm).Nodup) (hc : (supG s).Connected) : connected s = true := by
  unfold connected
  split
  · rfl
  · next v rest hv =>
    rw [List.all_eq_true]
    intro w hw
    have hvS : v ∈ (verts s).toFinset := by simp [hv]
    have hwS : w ∈ (verts s).toFinset := by simpa using hw
    obtain ⟨p⟩ := hc.preconnected ⟨v, hvS⟩ ⟨w, hwS⟩
    have hlen : p.bypass.length ≤ s.length := by
      rw [← card_edgeFinset_eq_length hloop hnd]
      exact p.bypass_isPath.isTrail.length_le_card_edgeFinset
    have := walk_reach p.bypass s.length [v] hlen (by simp)
    simpa using this

/-! ## One support -/

/-- A nonempty simple, two-coloured support with at most six links, codegree at most two and
no vertex of degree one is a single connected 4- or 6-cycle in the sense of
`TailFloor.shortCycle`. -/
theorem shortCycle_of (s : Graph) (col : ℕ → Bool)
    (hloop : ∀ e ∈ s, e.1 ≠ e.2) (hnd : (s.map norm).Nodup)
    (hbip : ∀ e ∈ s, col e.1 ≠ col e.2)
    (hcod : ∀ u v, u ≠ v → ∀ T : Finset ℕ, (∀ w ∈ T, adjP s u w ∧ adjP s v w) → #T ≤ 2)
    (hne : s ≠ []) (hlen : s.length ≤ 6) (hadm : admissible s = true) :
    shortCycle s = true := by
  classical
  let G := supG s
  let A : Finset (Sup s) := univ.filter (fun v => col v.1 = true)
  let B : Finset (Sup s) := univ.filter (fun v => col v.1 = false)
  have hbipG : G.IsBipartiteWith ↑A ↑B := by
    refine ⟨?_, ?_⟩
    · rw [Finset.disjoint_coe, Finset.disjoint_filter]; intro v _ h; simp [h]
    · intro v w hvw
      rcases (supG_adj.1 hvw).2 with h | h
      · have := hbip _ h
        cases hv : col v.1 <;> cases hw : col w.1 <;> simp_all [A, B]
      · have := hbip _ h
        cases hv : col v.1 <;> cases hw : col w.1 <;> simp_all [A, B]
  have hcov : ∀ v, v ∈ A ∨ v ∈ B := by
    intro v; cases h : col v.1 <;> simp [A, B, h]
  have hpair : ∀ a b, a ≠ b → #(G.neighborFinset a ∩ G.neighborFinset b) ≤ 2 := by
    intro a b hab
    rw [← Finset.card_map (Function.Embedding.subtype _)]
    apply hcod a.1 b.1 (fun h => hab (Subtype.ext h))
    intro w hw
    simp only [Finset.mem_map, Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      Function.Embedding.coe_subtype] at hw
    obtain ⟨x, ⟨h1, h2⟩, rfl⟩ := hw
    exact ⟨(supG_adj.1 h1).2, (supG_adj.1 h2).2⟩
  have hmin : ∀ v, 2 ≤ G.degree v := by
    intro v
    rw [degree_eq_deg hloop hnd]
    have hv : v.1 ∈ verts s := List.mem_toFinset.1 v.2
    have h1 := List.all_eq_true.1 hadm v.1 hv
    simp only [bne_iff_ne, ne_eq] at h1
    obtain ⟨e, he, hev⟩ := (mem_verts s v.1).1 hv
    have : 0 < deg s v.1 := by
      unfold deg
      exact List.length_pos_of_mem (List.mem_filter.2 ⟨he, by simpa using hev⟩)
    omega
  have hE : #G.edgeFinset ≤ 6 := by rw [card_edgeFinset_eq_length hloop hnd]; exact hlen
  obtain ⟨e0, he0⟩ := List.exists_mem_of_ne_nil s hne
  have : Nonempty (Sup s) := ⟨⟨e0.1, mem_sup.2 ⟨e0, he0, Or.inl rfl⟩⟩⟩
  obtain ⟨hdeg, hconn, hcard⟩ :=
    StructuralSupport.small_support_is_cycle G A B hbipG hcov hpair hmin hE
  have hsum := G.sum_degrees_eq_twice_card_edges
  simp only [hdeg, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  have hlenV : s.length = Fintype.card (Sup s) := by
    rw [← card_edgeFinset_eq_length hloop hnd]
    have : #G.edgeFinset = Fintype.card (Sup s) := by omega
    exact this
  unfold shortCycle
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true]
  refine ⟨⟨by omega, ?_⟩, connected_of_connected hloop hnd hconn⟩
  intro v hv
  have := hdeg ⟨v, by simpa using hv⟩
  rw [degree_eq_deg hloop hnd] at this
  exact this

/-! ## Every small support of a host graph -/

theorem mem_choose : ∀ (k : ℕ) (l s : Graph), s ∈ TailFloor.choose k l → s.Sublist l ∧ s.length = k
  | 0, _, s, h => by simp [TailFloor.choose] at h; subst h; simp
  | _ + 1, [], s, h => by simp [TailFloor.choose] at h
  | k + 1, e :: es, s, h => by
    simp only [TailFloor.choose, List.mem_append, List.mem_map] at h
    rcases h with ⟨t, ht, rfl⟩ | h
    · obtain ⟨h1, h2⟩ := mem_choose k es t ht
      exact ⟨h1.cons_cons e, by simp [h2]⟩
    · obtain ⟨h1, h2⟩ := mem_choose (k + 1) es s h
      exact ⟨h1.cons e, h2⟩

/-- **General Layer 3.** On a host link list with no loops and no repeated link, a proper
two-colouring, and at most two common neighbours for any two distinct vertices, every
admissible support with at most six links is a single connected 4- or 6-cycle. -/
theorem smallSupportsAreCycles_of (g : Graph) (col : ℕ → Bool)
    (hloop : ∀ e ∈ g, e.1 ≠ e.2) (hnd : (g.map norm).Nodup)
    (hbip : ∀ e ∈ g, col e.1 ≠ col e.2)
    (hcod : ∀ u v, u ≠ v → ∀ T : Finset ℕ, (∀ w ∈ T, adjP g u w ∧ adjP g v w) → #T ≤ 2) :
    SmallSupportsAreCycles g := by
  intro s hs hadm
  simp only [smallSupports, List.mem_flatMap, List.mem_range] at hs
  obtain ⟨k, hk, hsk⟩ := hs
  obtain ⟨hsub, hlen⟩ := mem_choose _ _ _ hsk
  have hsubset := hsub.subset
  have hadj : ∀ u w, adjP s u w → adjP g u w := fun u w h => h.imp (@hsubset _) (@hsubset _)
  refine shortCycle_of s col (fun e he => hloop e (hsubset he)) ((hsub.map _).nodup hnd)
    (fun e he => hbip e (hsubset he))
    (fun u v huv T hT => hcod u v huv T (fun w hw => ⟨hadj _ _ (hT w hw).1, hadj _ _ (hT w hw).2⟩))
    ?_ (by omega) hadm
  rintro rfl; simp at hlen

/-- `smallSupportsAreCycles_of` with the host conditions as Boolean checks. -/
theorem smallSupportsAreCycles_of_check (g : Graph) (col : ℕ → Bool)
    (hs : simpleB g = true) (hb : bipB col g = true) (hc : codeg2B g = true) :
    SmallSupportsAreCycles g :=
  smallSupportsAreCycles_of g col (simpleB_sound hs).1 (simpleB_sound hs).2 (bipB_sound hb)
    (codeg2B_sound hc)

/-! ## The test graphs, from the cheap checks only -/

/-- parity colouring of the cube and double cube (x·4 + y·2 + z labels) -/
def boxCol (v : ℕ) : Bool := (v / 4 + v / 2 + v) % 2 == 1

theorem two_cycles_of_codegree : SmallSupportsAreCycles twoE :=
  smallSupportsAreCycles_of_check twoE (fun v => (v % 3 + v / 3) % 2 == 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem strip_cycles_of_codegree : SmallSupportsAreCycles stripE :=
  smallSupportsAreCycles_of_check stripE (fun v => (v % 4 + v / 4) % 2 == 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem corner_cycles_of_codegree : SmallSupportsAreCycles cornerE :=
  smallSupportsAreCycles_of_check cornerE boxCol (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem cube_cycles_of_codegree : SmallSupportsAreCycles cubeE :=
  smallSupportsAreCycles_of_check cubeE boxCol (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- The 20-link double cube, with no enumeration of its supports. -/
theorem dcube_cycles_of_codegree : SmallSupportsAreCycles dcubeE :=
  smallSupportsAreCycles_of_check dcubeE boxCol (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-! ## Control: `K_{2,3}` is simple and bipartite but fails the codegree check -/

theorem k23_simple_bipartite : simpleB k23E = true ∧ bipB (fun v => v < 2) k23E = true := by
  decide +kernel

theorem k23_codegree_fails : codeg2B k23E = false := by decide +kernel

end SmallSupportBridge
