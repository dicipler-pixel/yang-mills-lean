import GraphInstances

/-!
# Short or long: one statement per graph

Author: Jeromie Beasley (Lean Green PR Machine, Grok Bot), with the Team.
ORCID https://orcid.org/0009-0006-4645-5643 · GitHub dicipler-pixel · X @d1c1pler ·
YouTube @AtlasMemoriae · atlas-memoriae.dicipler.workers.dev

For a nonzero gauge-invariant component with at least one non-trivial link, under the named
hypothesis `PeterWeylLattice` alone (every irrep simple), exactly one of two cases holds:
* **short:** `#NT = 4 ∨ #NT = 6`, and the non-trivial links form a single connected 4- or
  6-cycle (`TailFloor.shortCycle`);
* **long:** `6 < #NT`, and the conclusion of `TailFloor.long_support_floor` holds at `n = #NT`:
  every list of `#NT` link costs, each at least `4`, sums to at least `28`.

`TailFloor.long_support_floor` is
`(n) (cs : List Nat) (hlen : cs.length = n) (hn : n ≥ 7) (hc : ∀ x ∈ cs, x ≥ 4) : cs.sum ≥ 28`.
Its cost hypothesis `hc` (every non-trivial link costs at least `4`, i.e. `C₂ ≥ 4/3`) is kept
as the premise of the long case, not assumed. `long_energy_floor` discharges it for a Dynkin
labelling through `TailFloor.c3_nontrivial`. That needs one extra, explicitly named
hypothesis tying the labels to non-triviality: a non-trivial link carries a label
`(p, q) ≠ (0, 0)`.

Theorems: `list_support_dichotomy` (generic `listΓ`), `cube_support_dichotomy`,
`two_support_dichotomy`, `strip_support_dichotomy`, `corner_support_dichotomy`,
`dcube_support_dichotomy`, and `long_energy_floor`.
-/

open CategoryTheory TailFloor GaugeSupport SmallSupportBridge NtListSupport PermCube
  GraphInstances
open scoped Classical

namespace SupportDichotomy

universe u v

/-- **Generic dichotomy on `listΓ g n`.** -/
theorem list_support_dichotomy {k : Type u} {G : Type v} [Field k] [Group G]
    (g : Graph) (n : ℕ) (hmem : LinksIn g n) (hinj : NormInj g n) (hs : simpleB g = true)
    (hSSAC : SmallSupportsAreCycles g)
    {Irr : Type*} {irr : Irr → FDRep k G} [∀ i, Simple (irr i)] {H : Type*} [AddCommGroup H]
    [Module k H] {gauge : Representation k (Fin (n + 1) → G) H}
    (PW : PeterWeylLattice k G (listΓ g n) Irr irr H gauge)
    (ψ : H) (hψ : ∀ g, gauge g ψ = ψ) (π : Fin g.length → Irr) (hπ : PW.proj π ψ ≠ 0)
    (h1 : 1 ≤ (Finset.univ.filter (NTe (irr ∘ π))).card) :
    (((Finset.univ.filter (NTe (irr ∘ π))).card = 4 ∨
        (Finset.univ.filter (NTe (irr ∘ π))).card = 6) ∧
      shortCycle (supportList (listΓ g n) (irr ∘ π) Fin.val) = true) ∨
    (6 < (Finset.univ.filter (NTe (irr ∘ π))).card ∧
      ∀ cs : List ℕ, cs.length = (Finset.univ.filter (NTe (irr ∘ π))).card →
        (∀ x ∈ cs, x ≥ 4) → cs.sum ≥ 28) := by
  by_cases h6 : (Finset.univ.filter (NTe (irr ∘ π))).card ≤ 6
  · exact Or.inl ⟨list_gauge_support_card g n hmem hinj hs hSSAC PW ψ hψ π hπ h1 h6,
      list_gauge_support_shortCycle g n hmem hinj hs hSSAC PW ψ hψ π hπ h1 h6⟩
  · exact Or.inr ⟨by omega, fun cs hl hc => long_support_floor _ cs hl (by omega) hc⟩

section Graphs

variable {k : Type u} {G : Type v} [Field k] [Group G]
  {Irr : Type*} {irr : Irr → FDRep k G} [∀ i, Simple (irr i)] {H : Type*} [AddCommGroup H]
  [Module k H]

/-- **Cube.** -/
theorem cube_support_dichotomy {gauge : Representation k (Fin 8 → G) H}
    (PW : PeterWeylLattice k G cubeΓ Irr irr H gauge)
    (ψ : H) (hψ : ∀ g, gauge g ψ = ψ) (π : Fin 12 → Irr) (hπ : PW.proj π ψ ≠ 0)
    (h1 : 1 ≤ (Finset.univ.filter (NTe (irr ∘ π))).card) :
    (((Finset.univ.filter (NTe (irr ∘ π))).card = 4 ∨
        (Finset.univ.filter (NTe (irr ∘ π))).card = 6) ∧
      shortCycle (supportList cubeΓ (irr ∘ π) Fin.val) = true) ∨
    (6 < (Finset.univ.filter (NTe (irr ∘ π))).card ∧
      ∀ cs : List ℕ, cs.length = (Finset.univ.filter (NTe (irr ∘ π))).card →
        (∀ x ∈ cs, x ≥ 4) → cs.sum ≥ 28) := by
  by_cases h6 : (Finset.univ.filter (NTe (irr ∘ π))).card ≤ 6
  · exact Or.inl ⟨cube_gauge_support_card PW ψ hψ π hπ h1 h6,
      cube_gauge_support_shortCycle PW ψ hψ π hπ h1 h6⟩
  · exact Or.inr ⟨by omega, fun cs hl hc => long_support_floor _ cs hl (by omega) hc⟩

/-- **Two squares.** -/
theorem two_support_dichotomy {gauge : Representation k (Fin 6 → G) H}
    (PW : PeterWeylLattice k G twoΓ Irr irr H gauge)
    (ψ : H) (hψ : ∀ g, gauge g ψ = ψ) (π : Fin twoE.length → Irr) (hπ : PW.proj π ψ ≠ 0)
    (h1 : 1 ≤ (Finset.univ.filter (NTe (irr ∘ π))).card) :
    (((Finset.univ.filter (NTe (irr ∘ π))).card = 4 ∨
        (Finset.univ.filter (NTe (irr ∘ π))).card = 6) ∧
      shortCycle (supportList twoΓ (irr ∘ π) Fin.val) = true) ∨
    (6 < (Finset.univ.filter (NTe (irr ∘ π))).card ∧
      ∀ cs : List ℕ, cs.length = (Finset.univ.filter (NTe (irr ∘ π))).card →
        (∀ x ∈ cs, x ≥ 4) → cs.sum ≥ 28) :=
  list_support_dichotomy twoE 5 twoΓ_links twoΓ_norm_inj twoE_simple two_cycles PW ψ hψ π hπ h1

/-- **Three-square strip.** -/
theorem strip_support_dichotomy {gauge : Representation k (Fin 8 → G) H}
    (PW : PeterWeylLattice k G stripΓ Irr irr H gauge)
    (ψ : H) (hψ : ∀ g, gauge g ψ = ψ) (π : Fin stripE.length → Irr) (hπ : PW.proj π ψ ≠ 0)
    (h1 : 1 ≤ (Finset.univ.filter (NTe (irr ∘ π))).card) :
    (((Finset.univ.filter (NTe (irr ∘ π))).card = 4 ∨
        (Finset.univ.filter (NTe (irr ∘ π))).card = 6) ∧
      shortCycle (supportList stripΓ (irr ∘ π) Fin.val) = true) ∨
    (6 < (Finset.univ.filter (NTe (irr ∘ π))).card ∧
      ∀ cs : List ℕ, cs.length = (Finset.univ.filter (NTe (irr ∘ π))).card →
        (∀ x ∈ cs, x ≥ 4) → cs.sum ≥ 28) :=
  list_support_dichotomy stripE 7 stripΓ_links stripΓ_norm_inj stripE_simple strip_cycles
    PW ψ hψ π hπ h1

/-- **Corner.** -/
theorem corner_support_dichotomy {gauge : Representation k (Fin 7 → G) H}
    (PW : PeterWeylLattice k G cornerΓ Irr irr H gauge)
    (ψ : H) (hψ : ∀ g, gauge g ψ = ψ) (π : Fin cornerE.length → Irr) (hπ : PW.proj π ψ ≠ 0)
    (h1 : 1 ≤ (Finset.univ.filter (NTe (irr ∘ π))).card) :
    (((Finset.univ.filter (NTe (irr ∘ π))).card = 4 ∨
        (Finset.univ.filter (NTe (irr ∘ π))).card = 6) ∧
      shortCycle (supportList cornerΓ (irr ∘ π) Fin.val) = true) ∨
    (6 < (Finset.univ.filter (NTe (irr ∘ π))).card ∧
      ∀ cs : List ℕ, cs.length = (Finset.univ.filter (NTe (irr ∘ π))).card →
        (∀ x ∈ cs, x ≥ 4) → cs.sum ≥ 28) :=
  list_support_dichotomy cornerE 6 cornerΓ_links cornerΓ_norm_inj cornerE_simple corner_cycles
    PW ψ hψ π hπ h1

/-- **Double cube.** -/
theorem dcube_support_dichotomy {gauge : Representation k (Fin 12 → G) H}
    (PW : PeterWeylLattice k G dcubeΓ Irr irr H gauge)
    (ψ : H) (hψ : ∀ g, gauge g ψ = ψ) (π : Fin dcubeE.length → Irr) (hπ : PW.proj π ψ ≠ 0)
    (h1 : 1 ≤ (Finset.univ.filter (NTe (irr ∘ π))).card) :
    (((Finset.univ.filter (NTe (irr ∘ π))).card = 4 ∨
        (Finset.univ.filter (NTe (irr ∘ π))).card = 6) ∧
      shortCycle (supportList dcubeΓ (irr ∘ π) Fin.val) = true) ∨
    (6 < (Finset.univ.filter (NTe (irr ∘ π))).card ∧
      ∀ cs : List ℕ, cs.length = (Finset.univ.filter (NTe (irr ∘ π))).card →
        (∀ x ∈ cs, x ≥ 4) → cs.sum ≥ 28) :=
  list_support_dichotomy dcubeE 11 dcubeΓ_links dcubeΓ_norm_inj dcubeE_simple
    dcube_cycles_of_codegree PW ψ hψ π hπ h1

end Graphs

/-- **Long case with Dynkin labels.** If each irrep carries labels `lbl i = (p, q)`, and a
non-trivial link has `(p, q) ≠ (0, 0)` (the named labelling hypothesis `hnt`), then more than
six non-trivial links cost at least `28` in `c3 = 3·C₂` units. This is
`TailFloor.long_support_floor` with its cost hypothesis discharged by
`TailFloor.c3_nontrivial`. -/
theorem long_energy_floor {k : Type u} {G : Type v} [Field k] [Group G] {E : Type*} [Fintype E]
    {Irr : Type*} (irr : Irr → FDRep k G) (π : E → Irr) (lbl : Irr → ℕ × ℕ)
    (hnt : ∀ e, NTe (irr ∘ π) e → (lbl (π e)).1 + (lbl (π e)).2 ≥ 1)
    (hlong : 6 < (Finset.univ.filter (NTe (irr ∘ π))).card) :
    (((Finset.univ.filter (NTe (irr ∘ π))).toList).map
      (fun e => c3 (lbl (π e)).1 (lbl (π e)).2)).sum ≥ 28 := by
  refine long_support_floor _ _ (by simp) hlong ?_
  intro x hx
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ,
    true_and] at hx
  obtain ⟨e, he, rfl⟩ := hx
  exact c3_nontrivial _ _ (hnt e he)

/-! ## The 3-link strip sublist used by the control -/

/-- Three consecutive links `0-1-2-3` of the strip: a 3-link sublist of `stripE`. -/
def stripThree : Graph := [(0, 1), (1, 2), (2, 3)]

theorem stripThree_sublist : stripThree.Sublist stripE := by decide

/-- It is not a short cycle. -/
theorem stripThree_not_shortCycle : shortCycle stripThree = false := by decide

end SupportDichotomy
