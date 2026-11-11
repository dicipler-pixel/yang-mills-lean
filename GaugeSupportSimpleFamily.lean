/-
GaugeSupportSimpleFamily.lean — a complete family of simple representations for every finite
group, and the gauge support rule with no hypotheses left (Grey, 2026-11-11).

Closes the open item of `GaugeSupportPeterWeylFinite.lean`: there `IsCompleteIrrFamily irr`
(plus `Simple (irr i)` for the support rule) was a hypothesis. Here, for every finite `G`:
* `Irr := SimpleIdeal G`, the simple left ideals `m` of `ℂ[G] = MonoidAlgebra ℂ G` (a type in
  `Type`); `simpleIrr m := FDRep.of (Representation.ofModule m)` (left multiplication).
  Duplicates (isomorphic ideals) are allowed; completeness does not need them distinct.
* (a) `simple_of_isIrreducible`: an irreducible `Representation` on a finite-dimensional space
  is `Simple` in `FDRep` (a mono has stable range, `⊥` or `⊤`; uses `injective_of_mono`,
  `isIso_of_bijective` from `DualSimple`). With Mathlib's
  `isSimpleModule_iff_irreducible_ofModule` this gives `simpleIrr_simple`.
* (b) `exists_simpleIdeal_equiv`: every finite-dimensional irreducible `σ` is isomorphic to
  some `ofModule m`: for `w₀ ≠ 0` the orbit map `r ↦ r • w₀` is nonzero on some simple ideal
  (they span `ℂ[G]`, `span_simple_elements`, Maschke), and a nonzero intertwiner between
  irreducibles is bijective (kernel and range are stable). Hence
  `isCompleteIrrFamily_simpleIrr`.
* `peterWeylLinks_simpleIrr`, `gauge_support_rule_links_finite_unconditional`.
* Negation: `not_simple_regularRep` / `not_isIrreducible_regularRep` (constants are a proper
  stable line), `not_simple_regularRep_S3`.
set_option disclosure: `backward.isDefEq.respectTransparency false` on `simpleIrr`,
`ofModule_isIrreducible`, `simpleIrr_simple`, `simpleIrr_ρ`, `exists_simpleIdeal_equiv`
(instance-path unification for `RestrictScalars` modules, as in Mathlib's
`isSimpleModule_iff_irreducible_ofModule`). No `sorry`, no `native_decide`, no new axioms.
-/
import GaugeSupportPeterWeylFinite

open CategoryTheory MonoidalCategory Module

namespace GaugeSupport

variable {G : Type} [Group G]

/-! ### Irreducible representations give simple `FDRep`s -/

section Irreducible

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- In an irreducible representation, a `G`-stable subspace is `⊥` or `⊤`. -/
theorem eq_bot_or_eq_top_of_isIrreducible (ρ : Representation ℂ G V) (hρ : ρ.IsIrreducible)
    (W : Submodule ℂ V) (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  let S : Subrepresentation ρ := ⟨W, fun g _ hv => hW g _ hv⟩
  rcases hρ.eq_bot_or_eq_top S with h | h
  · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule h)

/-- An irreducible representation is nonzero. -/
theorem nontrivial_of_isIrreducible (ρ : Representation ℂ G V) (hρ : ρ.IsIrreducible) :
    Nontrivial V := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply hρ.bot_ne_top
  apply Subrepresentation.toSubmodule_injective
  exact Subsingleton.elim _ _

/-- **Irreducible ⇒ simple in `FDRep`.** -/
theorem simple_of_isIrreducible [Module.Finite ℂ V] (ρ : Representation ℂ G V)
    (hρ : ρ.IsIrreducible) : Simple (FDRep.of ρ) := by
  have hV := nontrivial_of_isIrreducible ρ hρ
  refine ⟨fun {Y} f _ => ⟨fun _ hf0 => ?_, fun hf0 => ?_⟩⟩
  · obtain ⟨v, hv⟩ := exists_ne (0 : V)
    obtain ⟨y, hy⟩ := (bijective_of_isIso f).2 v
    apply hv
    rw [← hy, hf0]
    rfl
  · let L : Y.V →ₗ[ℂ] V := f.hom.hom.hom
    have hU : ∀ g, ∀ v ∈ LinearMap.range L, ρ g v ∈ LinearMap.range L := by
      rintro g _ ⟨y, rfl⟩
      exact ⟨Y.ρ g y, congrArg (fun m => m.hom.hom y) (f.comm g)⟩
    rcases eq_bot_or_eq_top_of_isIrreducible ρ hρ _ hU with hbot | htop
    · exfalso
      apply hf0
      have hL : L = 0 := LinearMap.range_eq_bot.1 hbot
      ext y
      exact LinearMap.congr_fun hL y
    · exact isIso_of_bijective f ⟨injective_of_mono f, LinearMap.range_eq_top.1 htop⟩

end Irreducible

/-! ### The family of simple left ideals of `ℂ[G]` -/

section Ideals

/-- The index type: simple left ideals of `ℂ[G]` (in `Type`, like `FDRep ℂ G`'s carriers). -/
abbrev SimpleIdeal (G : Type) [Group G] :=
  {m : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G) // IsSimpleModule (MonoidAlgebra ℂ G) m}

variable [Fintype G]

instance instFiniteMonoidAlgebra : Module.Finite ℂ (MonoidAlgebra ℂ G) :=
  Module.Finite.of_basis (MonoidAlgebra.basis G ℂ)

instance instFiniteIdeal (m : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)) :
    Module.Finite ℂ (RestrictScalars ℂ (MonoidAlgebra ℂ G) m) :=
  Module.Finite.of_injective (idealIncl m) (idealIncl_injective m)

set_option backward.isDefEq.respectTransparency false in
/-- The simple left ideal `m` as a finite-dimensional representation (`G` acts by left
multiplication). -/
noncomputable def simpleIrr (m : SimpleIdeal G) : FDRep ℂ G :=
  FDRep.of (Representation.ofModule (k := ℂ) (G := G) m.1)

omit [Fintype G] in
set_option backward.isDefEq.respectTransparency false in
theorem ofModule_isIrreducible (m : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    [IsSimpleModule (MonoidAlgebra ℂ G) m] :
    (Representation.ofModule (k := ℂ) (G := G) m).IsIrreducible :=
  (Representation.isSimpleModule_iff_irreducible_ofModule m).1 inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- **Every member of the family is simple in `FDRep`.** -/
theorem simpleIrr_simple (m : SimpleIdeal G) : Simple (simpleIrr m) :=
  have := m.2
  simple_of_isIrreducible _ (ofModule_isIrreducible m.1)

set_option backward.isDefEq.respectTransparency false in
theorem simpleIrr_ρ (m : SimpleIdeal G) :
    (simpleIrr m).ρ = Representation.ofModule (k := ℂ) (G := G) m.1 := by
  unfold simpleIrr
  rfl

instance instSimpleIrr (m : SimpleIdeal G) : Simple (simpleIrr m) := simpleIrr_simple m

omit [Fintype G] in
theorem idealIncl_ofModule (m : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)) (u : G)
    (z : RestrictScalars ℂ (MonoidAlgebra ℂ G) m) :
    idealIncl m (Representation.ofModule (k := ℂ) (G := G) m u z) =
      MonoidAlgebra.single u 1 * idealIncl m z := by
  rw [← Representation.asAlgebraHom_single_one, Representation.ofModule_asAlgebraHom_apply_apply]
  show ((RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) m) ((RestrictScalars.addEquiv ℂ
    (MonoidAlgebra ℂ G) m).symm (MonoidAlgebra.single u 1 •
      RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) m z))).val = _
  rw [AddEquiv.apply_symm_apply, Submodule.coe_smul, smul_eq_mul]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Every finite-dimensional irreducible complex representation `σ` is isomorphic to some
simple left ideal. Route: for `w₀ ≠ 0`, the orbit map `r ↦ r • w₀` is nonzero on some simple
left ideal `m` (they span `ℂ[G]`, Maschke); restricted to `m` it is a nonzero intertwiner
between irreducibles, hence bijective (Schur's argument). -/
theorem exists_simpleIdeal_equiv (W : Type) [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W]
    (σ : Representation ℂ G W) (hσ : σ.IsIrreducible) :
    ∃ m : SimpleIdeal G, Nonempty (σ.Equiv (Representation.ofModule (k := ℂ) (G := G) m.1)) := by
  have hW := nontrivial_of_isIrreducible σ hσ
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : W)
  let φ : MonoidAlgebra ℂ G →ₗ[ℂ] W := LinearMap.applyₗ w₀ ∘ₗ σ.asAlgebraHom.toLinearMap
  have hφ1 : φ 1 = w₀ := by simp [φ]
  have hex : ∃ m : SimpleIdeal G, φ ∘ₗ idealIncl m.1 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hle : Submodule.span ℂ {w : MonoidAlgebra ℂ G | ∃ m : Submodule (MonoidAlgebra ℂ G)
        (MonoidAlgebra ℂ G), IsSimpleModule (MonoidAlgebra ℂ G) m ∧ w ∈ m} ≤
        LinearMap.ker φ := by
      rw [Submodule.span_le]
      rintro x ⟨m, hm, hx⟩
      have := LinearMap.congr_fun (hcon ⟨m, hm⟩)
        ((RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) m).symm ⟨x, hx⟩)
      rw [LinearMap.comp_apply, LinearMap.zero_apply] at this
      show φ x = 0
      convert this
      show x = ((RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) m)
        ((RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) m).symm ⟨x, hx⟩)).val
      rw [AddEquiv.apply_symm_apply]
    rw [span_simple_elements, top_le_iff] at hle
    apply hw₀
    rw [← hφ1]
    exact LinearMap.mem_ker.1 (hle ▸ Submodule.mem_top)
  obtain ⟨m, hm⟩ := hex
  have := m.2
  let ρm := Representation.ofModule (k := ℂ) (G := G) m.1
  let f : RestrictScalars ℂ (MonoidAlgebra ℂ G) m.1 →ₗ[ℂ] W := φ ∘ₗ idealIncl m.1
  have hf : ∀ (u : G) z, f (ρm u z) = σ u (f z) := by
    intro u z
    show σ.asAlgebraHom (idealIncl m.1 (ρm u z)) w₀ = σ u (σ.asAlgebraHom (idealIncl m.1 z) w₀)
    rw [idealIncl_ofModule, map_mul, Representation.asAlgebraHom_single_one]
    rfl
  have hinj : Function.Injective f := by
    rcases eq_bot_or_eq_top_of_isIrreducible ρm (ofModule_isIrreducible m.1) (LinearMap.ker f)
      (fun u z hz => by rw [LinearMap.mem_ker] at hz ⊢; rw [hf, hz, map_zero]) with h | h
    · exact LinearMap.ker_eq_bot.1 h
    · exact absurd (LinearMap.ker_eq_top.1 h) hm
  have hsurj : Function.Surjective f := by
    rcases eq_bot_or_eq_top_of_isIrreducible σ hσ (LinearMap.range f)
      (by rintro u _ ⟨z, rfl⟩; exact ⟨ρm u z, hf u z⟩) with h | h
    · exact absurd (LinearMap.range_eq_bot.1 h) hm
    · exact LinearMap.range_eq_top.1 h
  let e := LinearEquiv.ofBijective f ⟨hinj, hsurj⟩
  have E : ρm.Equiv σ := Representation.Equiv.mk e fun u => LinearMap.ext fun z => hf u z
  have E2 : σ.Equiv ρm := E.symm
  exact ⟨m, ⟨E2⟩⟩

/-- **The simple left ideals form a complete family.** -/
theorem isCompleteIrrFamily_simpleIrr : IsCompleteIrrFamily (simpleIrr (G := G)) := by
  intro W _ _ _ σ hσ
  obtain ⟨m, hm⟩ := exists_simpleIdeal_equiv W σ hσ
  refine ⟨m, ?_⟩
  rw [simpleIrr_ρ]
  exact hm

end Ideals

/-! ### Unconditional results for finite groups -/

section Unconditional

variable [Fintype G] {Vx E : Type*} [Fintype E] [DecidableEq E] (Γ : OrientedGraph Vx E)

/-- Peter–Weyl per link for every finite group over `ℂ`, with the family of simple left
ideals of `ℂ[G]`: no hypothesis. -/
theorem peterWeylLinks_simpleIrr :
    Nonempty (PeterWeylLinks ℂ G Γ (SimpleIdeal G) simpleIrr ((E → G) → ℂ) (latticeGauge Γ)) :=
  peterWeylLinks_of_finite Γ simpleIrr isCompleteIrrFamily_simpleIrr

/-- **The gauge support rule for finite groups with no hypotheses left**: labels are simple
left ideals of `ℂ[G]` (simple `FDRep`s, every irreducible occurring); for a gauge-invariant
`ψ : (E → G) → ℂ` and a labelling `π` with nonzero Fourier component, the nontrivial incident
factors at every vertex obey the one- and two-leg rules. -/
theorem gauge_support_rule_links_finite_unconditional [Fintype Vx] [DecidableEq Vx]
    (ψ : (E → G) → ℂ) (hψ : ∀ g, latticeGauge Γ g ψ = ψ)
    (π : E → SimpleIdeal G) (hπ : fourierProj simpleIrr π ψ ≠ 0) (v : Vx) :
    (∀ x, ntList (incident Γ (simpleIrr ∘ π) v) ≠ [x]) ∧
    (∀ x y, ntList (incident Γ (simpleIrr ∘ π) v) = [x, y] →
      (x.out = true → y.out = false → Nonempty (x.rep ≅ y.rep)) ∧
      (x.out = false → y.out = true → Nonempty (x.rep ≅ y.rep)) ∧
      (x.out = true → y.out = true → Nonempty (x.repᘁ ≅ y.rep)) ∧
      (x.out = false → y.out = false → Nonempty (x.rep ≅ y.repᘁ))) :=
  gauge_support_rule_links_finite Γ simpleIrr isCompleteIrrFamily_simpleIrr ψ hψ π hπ v

end Unconditional

/-! ### The regular representation is not simple -/

section Regular

/-- The (left) regular representation on `G → ℂ`: `(g · f)(t) = f (g⁻¹ * t)`. -/
noncomputable def regularRep (G : Type) [Group G] : Representation ℂ G (G → ℂ) where
  toFun g := LinearMap.funLeft ℂ ℂ (fun t => g⁻¹ * t)
  map_one' := by ext f t; simp [LinearMap.funLeft_apply]
  map_mul' g h := by ext f t; simp [LinearMap.funLeft_apply, mul_assoc]

theorem regularRep_apply (g : G) (f : G → ℂ) (t : G) : regularRep G g f t = f (g⁻¹ * t) := rfl

/-- The constants form a proper nonzero `G`-stable line once `G` is nontrivial. -/
theorem regularRep_const_line (g₀ : G) (hg₀ : g₀ ≠ 1) :
    let W : Submodule ℂ (G → ℂ) := Submodule.span ℂ {fun _ => 1}
    (∀ g, ∀ f ∈ W, regularRep G g f ∈ W) ∧ W ≠ ⊥ ∧ W ≠ ⊤ := by
  classical
  intro W
  refine ⟨fun g f hf => ?_, ?_, ?_⟩
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hf
    exact Submodule.mem_span_singleton.2 ⟨c, by ext t; simp [regularRep_apply]⟩
  · rw [Ne, Submodule.span_singleton_eq_bot]
    intro h
    simpa using congrFun h 1
  · intro h
    have hmem : Pi.single 1 1 ∈ W := h ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
    have h1 := congrFun hc 1
    have h2 := congrFun hc g₀
    simp [hg₀] at h1 h2
    simp [h2] at h1

/-- **The regular representation of a nontrivial finite group is not simple.** -/
theorem not_simple_regularRep [Finite G] (g₀ : G) (hg₀ : g₀ ≠ 1) :
    ¬ Simple (FDRep.of (regularRep G)) := by
  intro hS
  obtain ⟨hW, hbot, htop⟩ := regularRep_const_line g₀ hg₀
  rcases eq_bot_or_eq_top_of_simple (FDRep.of (regularRep G)) _ hW with h | h
  · exact hbot h
  · exact htop h

theorem not_isIrreducible_regularRep (g₀ : G) (hg₀ : g₀ ≠ 1) : ¬ (regularRep G).IsIrreducible :=
  fun h => by
    obtain ⟨hW, hbot, htop⟩ := regularRep_const_line g₀ hg₀
    rcases eq_bot_or_eq_top_of_isIrreducible _ h _ hW with h | h
    · exact hbot h
    · exact htop h

/-- For `S₃`: the 6-dimensional regular representation is not simple. -/
theorem not_simple_regularRep_S3 : ¬ Simple (FDRep.of (regularRep (Equiv.Perm (Fin 3)))) :=
  not_simple_regularRep (Equiv.swap 0 1) (by decide)

end Regular

end GaugeSupport

#print axioms GaugeSupport.simple_of_isIrreducible
#print axioms GaugeSupport.simpleIrr_simple
#print axioms GaugeSupport.exists_simpleIdeal_equiv
#print axioms GaugeSupport.isCompleteIrrFamily_simpleIrr
#print axioms GaugeSupport.peterWeylLinks_simpleIrr
#print axioms GaugeSupport.gauge_support_rule_links_finite_unconditional
#print axioms GaugeSupport.not_simple_regularRep
#print axioms GaugeSupport.not_isIrreducible_regularRep
#print axioms GaugeSupport.not_simple_regularRep_S3
