/-
GaugeSupport.lean — representation-theoretic core of the SU(3) gauge support rule.

Elementary, self-contained Schur arguments for an arbitrary group `G` acting linearly
on vector spaces over an arbitrary field `k` (no algebraic closure, no finite
dimensionality, no compactness needed for these two statements).

A representation is a monoid hom `G →* (V →ₗ[k] V)`, which is definitionally Mathlib's
`Representation k G V`. Irreducibility is stated directly via invariant subspaces so that
the file only depends on basic linear algebra.

No `sorry`, no `native_decide`, no new axioms.
-/
import Mathlib.LinearAlgebra.Span.Basic

namespace GaugeSupport

variable {G k V W : Type*} [Group G] [Field k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- A subspace stable under every `ρ g`. -/
def IsInvariant (ρ : G →* (V →ₗ[k] V)) (U : Submodule k V) : Prop :=
  ∀ g : G, ∀ v ∈ U, ρ g v ∈ U

/-- Irreducible (simple): nonzero, and the only invariant subspaces are `⊥` and `⊤`. -/
def IsIrreducible (ρ : G →* (V →ₗ[k] V)) : Prop :=
  Nontrivial V ∧ ∀ U : Submodule k V, IsInvariant ρ U → U = ⊥ ∨ U = ⊤

/-- The representation is non-trivial: some group element acts by a non-identity map. -/
def IsNontrivialRep (ρ : G →* (V →ₗ[k] V)) : Prop :=
  ∃ g : G, ρ g ≠ 1

/-- `f` intertwines `ρ` and `σ`. -/
def IsEquivariant (ρ : G →* (V →ₗ[k] V)) (σ : G →* (W →ₗ[k] W)) (f : V →ₗ[k] W) : Prop :=
  ∀ g : G, ∀ v : V, f (ρ g v) = σ g (f v)

/-- **Dangling-link rule (a).** An irreducible, non-trivial representation has no nonzero
invariant vector, i.e. `Hom_G(1, V) = 0`. -/
theorem no_invariant_single (ρ : G →* (V →ₗ[k] V)) (hirr : IsIrreducible ρ)
    (hnt : IsNontrivialRep ρ) (v : V) (hv : ∀ g : G, ρ g v = v) : v = 0 := by
  by_contra hv0
  obtain ⟨g₀, hg₀⟩ := hnt
  have hinv : IsInvariant ρ (k ∙ v) := by
    intro g u hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [map_smul, hv g]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self v)
  rcases hirr.2 _ hinv with hbot | htop
  · exact hv0 ((Submodule.span_singleton_eq_bot).mp hbot)
  · apply hg₀
    ext w
    have hw : w ∈ (k ∙ v) := htop ▸ Submodule.mem_top
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    simp [map_smul, hv g₀]

/-- **Schur's lemma** (field-agnostic form): an equivariant map between irreducible
representations is zero or bijective. -/
theorem schur (ρ : G →* (V →ₗ[k] V)) (σ : G →* (W →ₗ[k] W))
    (hρ : IsIrreducible ρ) (hσ : IsIrreducible σ) (f : V →ₗ[k] W)
    (hf : IsEquivariant ρ σ f) : f = 0 ∨ Function.Bijective f := by
  have hker : IsInvariant ρ (LinearMap.ker f) := by
    intro g v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hf, hv, map_zero]
  rcases hρ.2 _ hker with hk | hk
  · have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp hk
    have hrange : IsInvariant σ (LinearMap.range f) := by
      intro g w hw
      obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hw
      exact LinearMap.mem_range.mpr ⟨ρ g v, hf g v⟩
    rcases hσ.2 _ hrange with hr | hr
    · exact Or.inl (LinearMap.range_eq_bot.mp hr)
    · exact Or.inr ⟨hinj, LinearMap.range_eq_top.mp hr⟩
  · left
    ext v
    have : v ∈ LinearMap.ker f := hk ▸ Submodule.mem_top
    simpa using this

/-- Two representations are isomorphic: there is an equivariant linear equivalence. -/
def IsIso (ρ : G →* (V →ₗ[k] V)) (σ : G →* (W →ₗ[k] W)) : Prop :=
  ∃ e : V ≃ₗ[k] W, ∀ g : G, ∀ v : V, e (ρ g v) = σ g (e v)

/-- **Two-link rule (b), core form.** For irreducible `ρ, σ`, a nonzero intertwiner exists
iff `ρ ≅ σ`. Applied with `ρ := V*` (the dual of the incoming irrep) and `σ := W`, and using
`(V ⊗ W)^G ≅ Hom_G(V*, W)` for finite-dimensional `V`, this is the statement
"the invariant space of `V ⊗ W` is nonzero iff `W ≅ V*`". -/
theorem pair_invariant_iff_iso (ρ : G →* (V →ₗ[k] V)) (σ : G →* (W →ₗ[k] W))
    (hρ : IsIrreducible ρ) (hσ : IsIrreducible σ) :
    (∃ f : V →ₗ[k] W, IsEquivariant ρ σ f ∧ f ≠ 0) ↔ IsIso ρ σ := by
  constructor
  · rintro ⟨f, hf, hf0⟩
    rcases schur ρ σ hρ hσ f hf with h | h
    · exact absurd h hf0
    · exact ⟨LinearEquiv.ofBijective f h, fun g v => hf g v⟩
  · rintro ⟨e, he⟩
    refine ⟨e.toLinearMap, he, ?_⟩
    intro h0
    have := hρ.1
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    apply hv
    apply e.injective
    have := LinearMap.congr_fun h0 v
    simpa using this

/-- Contrapositive of (b), the form used for supports: if the two irreps at a 2-valent
vertex are not isomorphic, every intertwiner (hence every invariant) vanishes. -/
theorem pair_invariant_zero_of_not_iso (ρ : G →* (V →ₗ[k] V)) (σ : G →* (W →ₗ[k] W))
    (hρ : IsIrreducible ρ) (hσ : IsIrreducible σ) (hne : ¬ IsIso ρ σ)
    (f : V →ₗ[k] W) (hf : IsEquivariant ρ σ f) : f = 0 := by
  by_contra h0
  exact hne ((pair_invariant_iff_iso ρ σ hρ hσ).mp ⟨f, hf, h0⟩)

end GaugeSupport
