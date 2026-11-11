/-
CubeFiniteUnconditional.lean — the cube support theorems for finite gauge groups with no
Peter–Weyl assumption (Grey, 2026-11-11).

Lean Green's cube theorems (`PermCube.cube_gauge_support_shortCycle`, `_card`,
`SupportDichotomy.cube_support_dichotomy`) take the named hypothesis `PeterWeylLattice` and
`[∀ i, Simple (irr i)]`. For a finite group `G` both are now proved:
* `simpleIrr : SimpleIdeal G → FDRep ℂ G` (simple left ideals of `ℂ[G]`) is a complete family
  of simple representations (`simpleIrr_simple`, `isCompleteIrrFamily_simpleIrr`);
* `peterWeylLinksFinite cubeΓ simpleIrr _` is `PeterWeylLinks` on `H = (Fin 12 → G) → ℂ` with
  `latticeGauge cubeΓ`, and `.toLattice` turns it into `PeterWeylLattice`.
The projection of `.toLattice` is `reshuffle ∘ fourierProj simpleIrr π`; the reshuffle is a
linear isomorphism, so `fourierProj simpleIrr π ψ ≠ 0` transfers (`toLattice_proj_ne_zero`).
The cube side conditions (link endpoints in `cubeE`, injective normalised links, simple host,
`cube_cycles`) are already discharged inside Lean Green's cube theorems.

Results (any finite `G`, and `S₃ = Equiv.Perm (Fin 3)`): a nonzero gauge-invariant Fourier
component with 1 to 6 non-trivial links has exactly 4 or 6 of them, forming a short cycle;
with at least one non-trivial link it is short-or-long (`cube_support_dichotomy_finite`).
No set_option, no `sorry`, no `native_decide`, no new axioms.
-/
import GaugeSupportSimpleFamily
import SupportDichotomy

open CategoryTheory TailFloor GaugeSupport NtListSupport PermCube SupportDichotomy
open scoped Classical

namespace GaugeSupport

section Cube

variable {G : Type} [Group G] [Fintype G]

/-- The proved lattice Peter–Weyl structure on the cube for a finite group. -/
noncomputable abbrev cubePW (G : Type) [Group G] [Fintype G] :
    PeterWeylLattice ℂ G cubeΓ (SimpleIdeal G) simpleIrr ((Fin 12 → G) → ℂ)
      (latticeGauge cubeΓ) :=
  (peterWeylLinksFinite cubeΓ simpleIrr isCompleteIrrFamily_simpleIrr).toLattice

/-- `cubePW.proj = reshuffle ∘ fourierProj`, so a nonzero Fourier component stays nonzero. -/
theorem cubePW_proj_ne_zero (ψ : (Fin 12 → G) → ℂ) (π : Fin 12 → SimpleIdeal G)
    (hπ : fourierProj simpleIrr π ψ ≠ 0) : (cubePW G).proj π ψ ≠ 0 :=
  toLattice_proj_ne_zero (peterWeylLinksFinite cubeΓ simpleIrr isCompleteIrrFamily_simpleIrr)
    ψ π hπ

/-- **Cube, finite group, no Peter–Weyl assumption**: the non-trivial links of a nonzero
gauge-invariant Fourier component, when there are 1 to 6 of them, form a short cycle. -/
theorem cube_gauge_support_shortCycle_finite (ψ : (Fin 12 → G) → ℂ)
    (hψ : ∀ g, latticeGauge cubeΓ g ψ = ψ) (π : Fin 12 → SimpleIdeal G)
    (hπ : fourierProj simpleIrr π ψ ≠ 0)
    (h1 : 1 ≤ (Finset.univ.filter (NTe (simpleIrr ∘ π))).card)
    (h6 : (Finset.univ.filter (NTe (simpleIrr ∘ π))).card ≤ 6) :
    shortCycle (supportList cubeΓ (simpleIrr ∘ π) Fin.val) = true :=
  cube_gauge_support_shortCycle (cubePW G) ψ hψ π (cubePW_proj_ne_zero ψ π hπ) h1 h6

/-- **Cube, finite group**: such a component has exactly 4 or 6 non-trivial links. -/
theorem cube_gauge_support_card_finite (ψ : (Fin 12 → G) → ℂ)
    (hψ : ∀ g, latticeGauge cubeΓ g ψ = ψ) (π : Fin 12 → SimpleIdeal G)
    (hπ : fourierProj simpleIrr π ψ ≠ 0)
    (h1 : 1 ≤ (Finset.univ.filter (NTe (simpleIrr ∘ π))).card)
    (h6 : (Finset.univ.filter (NTe (simpleIrr ∘ π))).card ≤ 6) :
    (Finset.univ.filter (NTe (simpleIrr ∘ π))).card = 4 ∨
      (Finset.univ.filter (NTe (simpleIrr ∘ π))).card = 6 :=
  cube_gauge_support_card (cubePW G) ψ hψ π (cubePW_proj_ne_zero ψ π hπ) h1 h6

/-- Both conclusions together. -/
theorem cube_gauge_support_finite (ψ : (Fin 12 → G) → ℂ)
    (hψ : ∀ g, latticeGauge cubeΓ g ψ = ψ) (π : Fin 12 → SimpleIdeal G)
    (hπ : fourierProj simpleIrr π ψ ≠ 0)
    (h1 : 1 ≤ (Finset.univ.filter (NTe (simpleIrr ∘ π))).card)
    (h6 : (Finset.univ.filter (NTe (simpleIrr ∘ π))).card ≤ 6) :
    ((Finset.univ.filter (NTe (simpleIrr ∘ π))).card = 4 ∨
      (Finset.univ.filter (NTe (simpleIrr ∘ π))).card = 6) ∧
    shortCycle (supportList cubeΓ (simpleIrr ∘ π) Fin.val) = true :=
  ⟨cube_gauge_support_card_finite ψ hψ π hπ h1 h6,
    cube_gauge_support_shortCycle_finite ψ hψ π hπ h1 h6⟩

/-- **Cube dichotomy, finite group, no Peter–Weyl assumption**: a nonzero gauge-invariant
Fourier component with at least one non-trivial link either has 4 or 6 non-trivial links
forming a short cycle, or more than 6, and then any list of per-link costs, each at least 4,
sums to at least 28 (`long_support_floor`). -/
theorem cube_support_dichotomy_finite (ψ : (Fin 12 → G) → ℂ)
    (hψ : ∀ g, latticeGauge cubeΓ g ψ = ψ) (π : Fin 12 → SimpleIdeal G)
    (hπ : fourierProj simpleIrr π ψ ≠ 0)
    (h1 : 1 ≤ (Finset.univ.filter (NTe (simpleIrr ∘ π))).card) :
    (((Finset.univ.filter (NTe (simpleIrr ∘ π))).card = 4 ∨
        (Finset.univ.filter (NTe (simpleIrr ∘ π))).card = 6) ∧
      shortCycle (supportList cubeΓ (simpleIrr ∘ π) Fin.val) = true) ∨
    (6 < (Finset.univ.filter (NTe (simpleIrr ∘ π))).card ∧
      ∀ cs : List ℕ, cs.length = (Finset.univ.filter (NTe (simpleIrr ∘ π))).card →
        (∀ x ∈ cs, x ≥ 4) → cs.sum ≥ 28) :=
  cube_support_dichotomy (cubePW G) ψ hψ π (cubePW_proj_ne_zero ψ π hπ) h1

/-- No nonzero gauge-invariant Fourier component on the cube has exactly 3 non-trivial links. -/
theorem cube_no_three_links_finite :
    ¬ ∃ ψ : (Fin 12 → G) → ℂ, (∀ g, latticeGauge cubeΓ g ψ = ψ) ∧
      ∃ π : Fin 12 → SimpleIdeal G, fourierProj simpleIrr π ψ ≠ 0 ∧
        (Finset.univ.filter (NTe (simpleIrr ∘ π))).card = 3 := by
  rintro ⟨ψ, hψ, π, hπ, h3⟩
  have h := cube_gauge_support_card_finite ψ hψ π hπ (by omega) (by omega)
  omega

end Cube

/-! ### `S₃` -/

section S3

/-- The cube with gauge group `S₃`. -/
abbrev S3 := Equiv.Perm (Fin 3)

theorem cube_gauge_support_card_S3 (ψ : (Fin 12 → S3) → ℂ)
    (hψ : ∀ g, latticeGauge cubeΓ g ψ = ψ) (π : Fin 12 → SimpleIdeal S3)
    (hπ : fourierProj simpleIrr π ψ ≠ 0)
    (h1 : 1 ≤ (Finset.univ.filter (NTe (simpleIrr ∘ π))).card)
    (h6 : (Finset.univ.filter (NTe (simpleIrr ∘ π))).card ≤ 6) :
    ((Finset.univ.filter (NTe (simpleIrr ∘ π))).card = 4 ∨
      (Finset.univ.filter (NTe (simpleIrr ∘ π))).card = 6) ∧
    shortCycle (supportList cubeΓ (simpleIrr ∘ π) Fin.val) = true :=
  cube_gauge_support_finite ψ hψ π hπ h1 h6

theorem cube_support_dichotomy_S3 (ψ : (Fin 12 → S3) → ℂ)
    (hψ : ∀ g, latticeGauge cubeΓ g ψ = ψ) (π : Fin 12 → SimpleIdeal S3)
    (hπ : fourierProj simpleIrr π ψ ≠ 0)
    (h1 : 1 ≤ (Finset.univ.filter (NTe (simpleIrr ∘ π))).card) :
    (((Finset.univ.filter (NTe (simpleIrr ∘ π))).card = 4 ∨
        (Finset.univ.filter (NTe (simpleIrr ∘ π))).card = 6) ∧
      shortCycle (supportList cubeΓ (simpleIrr ∘ π) Fin.val) = true) ∨
    (6 < (Finset.univ.filter (NTe (simpleIrr ∘ π))).card ∧
      ∀ cs : List ℕ, cs.length = (Finset.univ.filter (NTe (simpleIrr ∘ π))).card →
        (∀ x ∈ cs, x ≥ 4) → cs.sum ≥ 28) :=
  cube_support_dichotomy_finite ψ hψ π hπ h1

theorem cube_no_three_links_S3 :
    ¬ ∃ ψ : (Fin 12 → S3) → ℂ, (∀ g, latticeGauge cubeΓ g ψ = ψ) ∧
      ∃ π : Fin 12 → SimpleIdeal S3, fourierProj simpleIrr π ψ ≠ 0 ∧
        (Finset.univ.filter (NTe (simpleIrr ∘ π))).card = 3 :=
  cube_no_three_links_finite

/-- A genuine 3-link path `0-1-3-2` in the cube host list (in `cubeE` order). -/
def cubeThree : Graph := [(0, 1), (2, 3), (1, 3)]

theorem cubeThree_sublist : cubeThree.Sublist cubeE := by decide

theorem cubeThree_not_shortCycle : shortCycle cubeThree = false := by decide

end S3

end GaugeSupport

#print axioms GaugeSupport.cubePW_proj_ne_zero
#print axioms GaugeSupport.cube_gauge_support_shortCycle_finite
#print axioms GaugeSupport.cube_gauge_support_card_finite
#print axioms GaugeSupport.cube_gauge_support_finite
#print axioms GaugeSupport.cube_support_dichotomy_finite
#print axioms GaugeSupport.cube_no_three_links_finite
#print axioms GaugeSupport.cube_gauge_support_card_S3
#print axioms GaugeSupport.cube_support_dichotomy_S3
#print axioms GaugeSupport.cube_no_three_links_S3
#print axioms GaugeSupport.cubeThree_sublist
#print axioms GaugeSupport.cubeThree_not_shortCycle
