import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Small supports are short cycles, general proof with no search

A graph with at most six edges and every degree at least two, which is bipartite and in which
two distinct vertices share at most two neighbours, has every degree exactly two, is connected,
and has four or six vertices (so it is a single 4- or 6-cycle).

Author: Jeromie Beasley (ink between the stars, Grok Bot), with the Team.
ORCID https://orcid.org/0009-0006-4645-5643 · GitHub dicipler-pixel · X @d1c1pler ·
YouTube @AtlasMemoriae · atlas-memoriae.dicipler.workers.dev

Proof: every link has one end in each side, so each side's degree sum is the link count (≤ 6);
with minimum degree 2 each side has 2 or 3 vertices. Two vertices on one side then force the
other side to be their common neighbours, so it has 2 too (4-cycle); otherwise both sides have
3 vertices, there are exactly 6 links and every degree is 2. Two vertices on one side always
share a neighbour (2 + 2 > 3), which gives connectivity.

Open item: the bridge from this statement to the list-based `TailFloor.SmallSupportsAreCycles`
(relabelling a list support into a `SimpleGraph`) is not formalized here.
-/

open Finset

namespace StructuralSupport

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem card_side_le {A B : Finset V} (hbip : G.IsBipartiteWith ↑A ↑B)
    (hmin : ∀ v, 2 ≤ G.degree v) (hE : #G.edgeFinset ≤ 6) : #A ≤ 3 := by
  have hs := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hbip
  have : #A * 2 ≤ ∑ v ∈ A, G.degree v := by
    have := Finset.card_nsmul_le_sum A (fun v => G.degree v) 2 (fun v _ => hmin v)
    simpa [smul_eq_mul] using this
  omega

theorem nbr_subset {A B : Finset V} (hbip : G.IsBipartiteWith ↑A ↑B) {v : V} (hv : v ∈ A) :
    G.neighborFinset v ⊆ B := by
  intro w hw
  rw [SimpleGraph.mem_neighborFinset] at hw
  exact_mod_cast hbip.mem_of_mem_adj (by exact_mod_cast hv) hw

/-- if one side has two vertices, so does the other -/
theorem side_two {A B : Finset V} (hbip : G.IsBipartiteWith ↑A ↑B)
    (hpair : ∀ a b, a ≠ b → #(G.neighborFinset a ∩ G.neighborFinset b) ≤ 2)
    (hmin : ∀ v, 2 ≤ G.degree v) (hA : #A = 2) : #B ≤ 2 := by
  obtain ⟨a1, a2, hne, rfl⟩ := Finset.card_eq_two.mp hA
  have hsub : B ⊆ G.neighborFinset a1 ∩ G.neighborFinset a2 := by
    intro b hb
    have hN : G.neighborFinset b ⊆ {a1, a2} := nbr_subset G hbip.symm hb
    have hcard : #({a1, a2} : Finset V) ≤ #(G.neighborFinset b) := by
      rw [SimpleGraph.card_neighborFinset_eq_degree, hA]; exact hmin b
    have heq := Finset.eq_of_subset_of_card_le hN hcard
    have h1 : a1 ∈ G.neighborFinset b := by rw [heq]; simp
    have h2 : a2 ∈ G.neighborFinset b := by rw [heq]; simp
    rw [SimpleGraph.mem_neighborFinset] at h1 h2
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨h1.symm, h2.symm⟩
  exact (Finset.card_le_card hsub).trans (hpair a1 a2 hne)

theorem side_ge_two {A B : Finset V} (hbip : G.IsBipartiteWith ↑A ↑B)
    (hmin : ∀ v, 2 ≤ G.degree v) {v : V} (hv : v ∈ A) : 2 ≤ #B := by
  have h := hmin v
  rw [← SimpleGraph.card_neighborFinset_eq_degree] at h
  exact h.trans (Finset.card_le_card (nbr_subset G hbip hv))

theorem common_nbr {A B : Finset V} (hbip : G.IsBipartiteWith ↑A ↑B)
    (hmin : ∀ v, 2 ≤ G.degree v) (hB : #B ≤ 3) {a a' : V} (ha : a ∈ A) (ha' : a' ∈ A) :
    ∃ b, G.Adj a b ∧ G.Adj a' b := by
  have h1 := hmin a; have h2 := hmin a'
  rw [← SimpleGraph.card_neighborFinset_eq_degree] at h1 h2
  have hu : #(G.neighborFinset a ∪ G.neighborFinset a') ≤ 3 :=
    (Finset.card_le_card (Finset.union_subset (nbr_subset G hbip ha) (nbr_subset G hbip ha'))).trans hB
  have := Finset.card_union_add_card_inter (G.neighborFinset a) (G.neighborFinset a')
  obtain ⟨b, hb⟩ : (G.neighborFinset a ∩ G.neighborFinset a').Nonempty := by
    rw [← Finset.card_pos]; omega
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hb
  exact ⟨b, hb⟩

theorem small_support_is_cycle (A B : Finset V)
    (hbip : G.IsBipartiteWith ↑A ↑B) (hcov : ∀ v, v ∈ A ∨ v ∈ B)
    (hpair : ∀ a b, a ≠ b → #(G.neighborFinset a ∩ G.neighborFinset b) ≤ 2)
    (hmin : ∀ v, 2 ≤ G.degree v) (hE : #G.edgeFinset ≤ 6) [Nonempty V] :
    (∀ v, G.degree v = 2) ∧ G.Connected ∧ (Fintype.card V = 4 ∨ Fintype.card V = 6) := by
  have hA3 := card_side_le G hbip hmin hE
  have hB3 := card_side_le G hbip.symm hmin hE
  obtain ⟨v0⟩ := ‹Nonempty V›
  have hA2 : 2 ≤ #A ∧ 2 ≤ #B := by
    rcases hcov v0 with h | h
    · have hB := side_ge_two G hbip hmin h
      obtain ⟨w, hw⟩ : B.Nonempty := by rw [← Finset.card_pos]; omega
      exact ⟨side_ge_two G hbip.symm hmin hw, hB⟩
    · have hA := side_ge_two G hbip.symm hmin h
      obtain ⟨w, hw⟩ : A.Nonempty := by rw [← Finset.card_pos]; omega
      exact ⟨hA, side_ge_two G hbip hmin hw⟩
  have hsides : (#A = 2 ∧ #B = 2) ∨ (#A = 3 ∧ #B = 3) := by
    have k1 : #A = 2 → #B ≤ 2 := side_two G hbip hpair hmin
    have k2 : #B = 2 → #A ≤ 2 := side_two G hbip.symm hpair hmin
    omega
  have hcardV : Fintype.card V = #A + #B := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_coe.mp hbip.disjoint)]
    rw [← Finset.card_univ]; congr 1
    ext v; simp only [Finset.mem_univ, Finset.mem_union, true_iff]; exact hcov v
  refine ⟨?_, ?_, by omega⟩
  · -- every degree is two
    have side : ∀ {S T : Finset V}, G.IsBipartiteWith ↑S ↑T → (#S = 2 ∧ #T = 2) ∨ (#S = 3 ∧ #T = 3) →
        ∀ v ∈ S, G.degree v = 2 := by
      intro S T h hst v hv
      have hle : G.degree v ≤ #T := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        exact Finset.card_le_card (nbr_subset G h hv)
      rcases hst with ⟨_, hT⟩ | ⟨hS, _⟩
      · have := hmin v; omega
      · by_contra hne
        have hlt : ∑ w ∈ S, 2 < ∑ w ∈ S, G.degree w :=
          Finset.sum_lt_sum (fun w _ => hmin w) ⟨v, hv, by have := hmin v; omega⟩
        rw [SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges h] at hlt
        simp [hS] at hlt; omega
    intro v
    rcases hcov v with h | h
    · exact side hbip hsides v h
    · exact side hbip.symm (by omega) v h
  · -- connected: every vertex reaches a fixed vertex of A
    obtain ⟨a0, ha0⟩ : A.Nonempty := by rw [← Finset.card_pos]; omega
    have hB3' : #B ≤ 3 := hB3
    have toA : ∀ a ∈ A, G.Reachable a a0 := by
      intro a ha
      obtain ⟨b, h1, h2⟩ := common_nbr G hbip hmin hB3' ha ha0
      exact (SimpleGraph.Adj.reachable h1).trans (SimpleGraph.Adj.reachable h2.symm)
    have all : ∀ v, G.Reachable v a0 := by
      intro v
      rcases hcov v with h | h
      · exact toA v h
      · have hd := hmin v
        rw [← SimpleGraph.card_neighborFinset_eq_degree] at hd
        obtain ⟨a, ha⟩ : (G.neighborFinset v).Nonempty := by rw [← Finset.card_pos]; omega
        have haA := nbr_subset G hbip.symm h ha
        rw [SimpleGraph.mem_neighborFinset] at ha
        exact (SimpleGraph.Adj.reachable ha).trans (toA a haA)
    exact SimpleGraph.Connected.mk (fun u w => (all u).trans (all w).symm)

end StructuralSupport

