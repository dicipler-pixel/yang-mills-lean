/-
GaugeSupportReshuffle.lean — the edge-to-vertex reshuffle, proved (Grey, 2026-11-11).

Setting (as in `GaugeSupportLattice.lean` / `GaugeSupportRegroup.lean`): a finite oriented
graph `Γ`, finite vertex set, a finite-dimensional representation `π e : FDRep k G` on every
link. A link `e` has two ends (half-edges): `inl e` at `src e`, carrying `V_{π e}`, and
`inr e` at `tgt e`, carrying `V_{π e}*` (the convention of `incident`: outgoing ↦ `π e`,
incoming ↦ `(π e)ᘁ`). The vertex space `W_v = vertexRep (incident Γ π v)` is the right-nested
tensor product of the factors at `v`, outgoing links first, then incoming links, each in the
order of `Finset.toList` of the filtered edges, ending in `𝟙`.

Proved here (any group `G`, any field `k`; no `sorry`, no `native_decide`, no new axioms):
* `reshuffle : EdgeBlock π ≃ₗ[k] RegroupedBlock Γ π`, i.e. `⊗_e (V_{π e} ⊗ V_{π e}*) ≅ ⊗_v W_v`.
  It is built from three steps: `pairEquiv` (`⊗_e (A_e ⊗ B_e) ≅ ⊗_{h ∈ E ⊕ E} F_h`),
  `regroupEquiv` (`⊗_h F_h ≅ ⊗_v ⊗_{endpoint h = v} F_h`) and `vertexEquiv`
  (`⊗_{endpoint h = v} F_h ≅ W_v`, via `listEquiv`, `⊗_{i ∈ l} M_i ≅ M_{l₀} ⊗ (M_{l₁} ⊗ … 𝟙)`).
  The first two are linear maps defined on pure tensors, shown surjective (pure tensors span)
  and then bijective by comparing dimensions (`finrank_piTensorProduct`).
* `reshuffle_tprod`: on pure tensors it is the permutation of factors: `⊗_e (a_e ⊗ b_e)` goes
  to `⊗_v` (nested tensor of the `a_e`, `e` leaving `v`, and the `b_e`, `e` entering `v`).
* `reshuffle_equivariant` / `reshuffle_symm_equivariant`: it intertwines the link action
  `edgeGauge` (copy at `src e` on `V_{π e}`, copy at `tgt e` on `V_{π e}*`) with the vertex
  action `blockGauge` of `GaugeSupportRegroup` (copy at `v` on `W_v`).
* `PeterWeylLinks` (a structure, NOT an axiom): block projections `H → ⊗_e (V ⊗ V*)` that are
  equivariant for `edgeGauge` and separate points, i.e. Peter–Weyl link by link only.
  `PeterWeylLinks.toLattice` builds the old `PeterWeylLattice` from it with the proved
  reshuffle, so `gauge_support_rule_links` (and `_SU3`) give the regrouped support rule from
  the weaker assumption. `PeterWeylLinks.model` shows the assumption is inhabited.

Still assumed (not proved): Peter–Weyl for `L²(SU(3))` itself, i.e. that the physical lattice
Hilbert space with its gauge action satisfies `PeterWeylLinks`. Checked on Lean v4.33.0 /
Mathlib v4.33.0.
-/
import GaugeSupportRegroup
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
open CategoryTheory MonoidalCategory Module TensorProduct

namespace GaugeSupport
universe u v
variable {k : Type u} {G : Type v} [Field k] [Group G]

section ListStep
variable {ι : Type*} (M : ι → FDRep k G)

/-- Nested pure tensor along a list of indices. -/
noncomputable def listTmul : (l : List ι) → (∀ i : {i // i ∈ l}, M i) → tensorList (l.map M)
  | [], _ => (1 : k)
  | a :: l, f => (f ⟨a, List.mem_cons_self⟩ ⊗ₜ[k]
      listTmul l (fun i => f ⟨i.1, List.mem_cons_of_mem _ i.2⟩) : M a ⊗[k] tensorList (l.map M))

/-- Complement of the head in the index type of `a :: l` is the index type of `l`. -/
def consComplEquiv {a : ι} {l : List ι} (ha : a ∉ l) :
    (({⟨a, List.mem_cons_self⟩} : Set {i // i ∈ a :: l})ᶜ : Set {i // i ∈ a :: l}) ≃
      {i // i ∈ l} where
  toFun j := ⟨j.1.1, by
    rcases List.mem_cons.1 j.1.2 with h | h
    · exact absurd (Subtype.ext h) j.2
    · exact h⟩
  invFun i := ⟨⟨i.1, List.mem_cons_of_mem _ i.2⟩, fun h => ha (by
    have : i.1 = a := congrArg Subtype.val (Set.mem_singleton_iff.1 h); exact this ▸ i.2)⟩
  left_inv j := rfl
  right_inv i := rfl

/-- Reindexing the complement of the head. -/
noncomputable def reindexCons {a : ι} {l : List ι} (ha : a ∉ l) :
    (⨂[k] j : (({⟨a, List.mem_cons_self⟩} : Set {i // i ∈ a :: l})ᶜ : Set {i // i ∈ a :: l}),
      M j.1.1) ≃ₗ[k] ⨂[k] i : {i // i ∈ l}, M i.1 :=
  PiTensorProduct.reindex k _ (consComplEquiv ha)

theorem reindexCons_tprod {a : ι} {l : List ι} (ha : a ∉ l)
    (f : ∀ j : (({⟨a, List.mem_cons_self⟩} : Set {i // i ∈ a :: l})ᶜ : Set {i // i ∈ a :: l}),
      M j.1.1) :
    reindexCons M ha (PiTensorProduct.tprod k f) =
      PiTensorProduct.tprod k (fun i => f ((consComplEquiv ha).symm i)) :=
  PiTensorProduct.reindex_tprod _ _

/-- Splitting off the head of the list. -/
noncomputable def consEquiv [DecidableEq ι] {a : ι} {l : List ι} (ha : a ∉ l) :
    (⨂[k] i : {i // i ∈ a :: l}, M i.1) ≃ₗ[k] (M a ⊗[k] (⨂[k] i : {i // i ∈ l}, M i.1)) :=
  (PiTensorProduct.equivPiTensorComplSingletonTensor k (fun i : {i // i ∈ a :: l} => M i)
      ⟨a, List.mem_cons_self⟩).trans
    ((TensorProduct.comm k _ _).trans (LinearEquiv.lTensor (M a) (reindexCons M ha)))

theorem consEquiv_tprod [DecidableEq ι] {a : ι} {l : List ι} (ha : a ∉ l)
    (f : ∀ i : {i // i ∈ a :: l}, M i.1) :
    consEquiv M ha (PiTensorProduct.tprod k f) =
      f ⟨a, List.mem_cons_self⟩ ⊗ₜ[k]
        PiTensorProduct.tprod k (fun i : {i // i ∈ l} => f ⟨i.1, List.mem_cons_of_mem _ i.2⟩) := by
  show LinearEquiv.lTensor (M a) (reindexCons M ha) (TensorProduct.comm k _ _
    (PiTensorProduct.equivPiTensorComplSingletonTensor k (fun i : {i // i ∈ a :: l} => M i)
      ⟨a, List.mem_cons_self⟩ (PiTensorProduct.tprod k f))) = _
  rw [PiTensorProduct.equivPiTensorComplSingletonTensor_tprod, TensorProduct.comm_tmul,
    LinearEquiv.lTensor_tmul, reindexCons_tprod]
  rfl

/-- The empty list. -/
noncomputable def nilEquiv : (⨂[k] i : {i // i ∈ ([] : List ι)}, M i.1) ≃ₗ[k] k :=
  letI : IsEmpty {i // i ∈ ([] : List ι)} := ⟨fun i => List.not_mem_nil i.2⟩
  PiTensorProduct.isEmptyEquiv _

theorem nilEquiv_tprod (f : ∀ i : {i // i ∈ ([] : List ι)}, M i.1) :
    nilEquiv M (PiTensorProduct.tprod k f) = 1 := by
  unfold nilEquiv; simp

/-- `⨂_{i ∈ l} M i ≅ M l₀ ⊗ (M l₁ ⊗ (… ⊗ 𝟙))` for a list without repetitions. -/
noncomputable def listEquiv [DecidableEq ι] : (l : List ι) → l.Nodup →
    ((⨂[k] i : {i // i ∈ l}, M i) ≃ₗ[k] tensorList (l.map M))
  | [], _ => nilEquiv M
  | a :: l, h =>
    ((consEquiv M (List.nodup_cons.1 h).1).trans
      (LinearEquiv.lTensor (M a) (listEquiv l (List.nodup_cons.1 h).2)) :)

theorem listEquiv_tprod [DecidableEq ι] (l : List ι) (h : l.Nodup) (f : ∀ i : {i // i ∈ l}, M i) :
    listEquiv M l h (PiTensorProduct.tprod k f) = listTmul M l f := by
  induction l with
  | nil => exact nilEquiv_tprod M f
  | cons a l ih =>
    show LinearEquiv.lTensor (M a) (listEquiv M l (List.nodup_cons.1 h).2)
      (consEquiv M (List.nodup_cons.1 h).1 (PiTensorProduct.tprod k f)) = _
    rw [consEquiv_tprod, LinearEquiv.lTensor_tmul, ih]
    rfl

theorem listTmul_ρ (g : G) : (l : List ι) → (f : ∀ i : {i // i ∈ l}, M i) →
    listTmul M l (fun i => (M i).ρ g (f i)) = (tensorList (l.map M)).ρ g (listTmul M l f)
  | [], _ => rfl
  | a :: l, f => by
    rw [listTmul, listTmul, listTmul_ρ g l]
    rfl

/-- `listEquiv` is `G`-equivariant. -/
theorem listEquiv_equivariant [DecidableEq ι] (l : List ι) (h : l.Nodup) (g : G)
    (t : ⨂[k] i : {i // i ∈ l}, M i) :
    listEquiv M l h (PiTensorProduct.map (fun i => (M i.1).ρ g) t) =
      (tensorList (l.map M)).ρ g (listEquiv M l h t) := by
  have : (listEquiv M l h).toLinearMap ∘ₗ PiTensorProduct.map (fun i => (M i.1).ρ g) =
      (tensorList (l.map M)).ρ g ∘ₗ (listEquiv M l h).toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro f
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
      PiTensorProduct.map_tprod, LinearEquiv.coe_coe, listEquiv_tprod]
    exact listTmul_ρ M g l f
  exact LinearMap.congr_fun this t

end ListStep

section Sigma

variable {ι Vx : Type*} [Fintype ι] [Fintype Vx] [DecidableEq Vx] (p : ι → Vx)
  (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)]

omit [Fintype ι] [Fintype Vx] in
theorem update_fiber [DecidableEq ι] (f : ∀ i, M i) (i₀ : ι) (z : M i₀) :
    (fun v => PiTensorProduct.tprod k (fun j : {i // p i = v} => Function.update f i₀ z j.1)) =
      Function.update (fun v => PiTensorProduct.tprod k (fun j : {i // p i = v} => f j.1)) (p i₀)
        (PiTensorProduct.tprod k
          (Function.update (fun j : {i // p i = p i₀} => f j.1) ⟨i₀, rfl⟩ z)) := by
  funext v
  by_cases hv : v = p i₀
  · subst hv
    rw [Function.update_self]
    congr 1
    funext j
    by_cases hj : j.1 = i₀
    · obtain ⟨j, hj'⟩ := j
      dsimp only at hj
      subst hj
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hj, Function.update_of_ne (fun h => hj (congrArg Subtype.val h))]
  · rw [Function.update_of_ne hv]
    congr 1
    funext j
    rw [Function.update_of_ne (fun h => hv (j.2.symm.trans (congrArg p h)))]

/-- The regrouping map `f ↦ ⨂_v ⨂_{p i = v} f i` is multilinear. -/
noncomputable def regroupML : MultilinearMap k M (⨂[k] v, ⨂[k] j : {i // p i = v}, M j.1) where
  toFun f := PiTensorProduct.tprod k (fun v => PiTensorProduct.tprod k (fun j : {i // p i = v} => f j.1))
  map_update_add' f i₀ x y := by
    simp only [update_fiber, MultilinearMap.map_update_add]
  map_update_smul' f i₀ c x := by
    simp only [update_fiber, MultilinearMap.map_update_smul]

/-- The regrouping map `⨂_i M i → ⨂_v ⨂_{p i = v} M i`. -/
noncomputable def regroupMap [DecidableEq ι] :
    (⨂[k] i, M i) →ₗ[k] ⨂[k] v, ⨂[k] j : {i // p i = v}, M j.1 :=
  PiTensorProduct.lift (regroupML p M)

omit [Fintype ι] [Fintype Vx] in
theorem regroupMap_tprod [DecidableEq ι] (f : ∀ i, M i) :
    regroupMap p M (PiTensorProduct.tprod k f) =
      PiTensorProduct.tprod k (fun v => PiTensorProduct.tprod k (fun j : {i // p i = v} => f j.1)) :=
  PiTensorProduct.lift.tprod f

omit [Fintype ι] in
theorem regroupMap_surjective [DecidableEq ι] : Function.Surjective (regroupMap (k := k) p M) := by
  rw [← LinearMap.range_eq_top, eq_top_iff,
    ← PiTensorProduct.submodule_span_eq_top
      (g := fun v (x : ∀ j : {i // p i = v}, M j.1) => PiTensorProduct.tprod k x)
      (fun v => PiTensorProduct.span_tprod_eq_top), Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  refine ⟨PiTensorProduct.tprod k (fun i => x (p i) ⟨i, rfl⟩), ?_⟩
  rw [regroupMap_tprod]
  congr 1
  funext v
  congr 1
  funext j
  obtain ⟨j, rfl⟩ := j
  rfl

omit [Fintype Vx] [DecidableEq Vx] in
theorem finrank_piTensorProduct {κ : Type*} [Fintype κ] (N : κ → Type*)
    [∀ i, AddCommGroup (N i)] [∀ i, Module k (N i)] [∀ i, FiniteDimensional k (N i)] :
    finrank k (⨂[k] i, N i) = ∏ i, finrank k (N i) := by
  classical
  rw [Module.finrank_eq_card_basis
    (Basis.piTensorProduct (fun i => Module.Free.chooseBasis k (N i))), Fintype.card_pi]
  simp [Module.finrank_eq_card_chooseBasisIndex]

theorem regroupMap_injective [DecidableEq ι] [∀ i, FiniteDimensional k (M i)] :
    Function.Injective (regroupMap (k := k) p M) := by
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).2
    (regroupMap_surjective (k := k) p M)
  rw [finrank_piTensorProduct, finrank_piTensorProduct]
  simp only [finrank_piTensorProduct]
  exact (Fintype.prod_fiberwise p (fun i => finrank k (M i))).symm

/-- **Regrouping by fibres**: `⨂_i M i ≃ ⨂_v ⨂_{p i = v} M i` (finite-dimensional factors). -/
noncomputable def regroupEquiv [DecidableEq ι] [∀ i, FiniteDimensional k (M i)] :
    (⨂[k] i, M i) ≃ₗ[k] ⨂[k] v, ⨂[k] j : {i // p i = v}, M j.1 :=
  LinearEquiv.ofBijective (regroupMap p M) ⟨regroupMap_injective (k := k) p M, regroupMap_surjective (k := k) p M⟩

theorem regroupEquiv_tprod [DecidableEq ι] [∀ i, FiniteDimensional k (M i)] (f : ∀ i, M i) :
    regroupEquiv p M (PiTensorProduct.tprod k f) =
      PiTensorProduct.tprod k (fun v => PiTensorProduct.tprod k (fun j : {i // p i = v} => f j.1)) :=
  regroupMap_tprod p M f

/-- The regrouping intertwines factorwise maps. -/
theorem regroupEquiv_map [DecidableEq ι] [∀ i, FiniteDimensional k (M i)]
    (φ : ∀ i, M i →ₗ[k] M i) (t : ⨂[k] i, M i) :
    regroupEquiv p M (PiTensorProduct.map φ t) =
      PiTensorProduct.map (fun v => PiTensorProduct.map (fun j : {i // p i = v} => φ j.1))
        (regroupEquiv p M t) := by
  have : (regroupEquiv p M).toLinearMap ∘ₗ PiTensorProduct.map φ =
      PiTensorProduct.map (fun v => PiTensorProduct.map (fun j : {i // p i = v} => φ j.1)) ∘ₗ
        (regroupEquiv p M).toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro f
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
      PiTensorProduct.map_tprod, LinearEquiv.coe_coe, regroupEquiv_tprod]
  exact LinearMap.congr_fun this t

end Sigma

section Pairs

variable {E : Type*} [Fintype E] (F : E ⊕ E → FDRep k G)

/-- `⨂_h F h → ⨂_e (F (inl e) ⊗ F (inr e))`: pair the two ends of every edge. -/
noncomputable def pairMap :
    (⨂[k] h, F h) →ₗ[k] ⨂[k] e, (F (.inl e) ⊗[k] F (.inr e)) :=
  TensorProduct.lift (PiTensorProduct.map₂ (fun e => TensorProduct.mk k (F (.inl e)) (F (.inr e))))
    ∘ₗ (PiTensorProduct.tmulEquivDep k (fun h => (F h : Type u))).symm.toLinearMap

omit [Fintype E] in
theorem pairMap_tprod (f : ∀ h, F h) :
    pairMap F (PiTensorProduct.tprod k f) =
      PiTensorProduct.tprod k (fun e => f (.inl e) ⊗ₜ[k] f (.inr e)) := by
  simp only [pairMap, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    PiTensorProduct.tmulEquivDep_symm_apply, TensorProduct.lift.tmul,
    PiTensorProduct.map₂_tprod_tprod, TensorProduct.mk_apply]

theorem pairMap_surjective : Function.Surjective (pairMap F) := by
  rw [← LinearMap.range_eq_top, eq_top_iff,
    ← PiTensorProduct.submodule_span_eq_top
      (g := fun e (x : F (.inl e) × F (.inr e)) => x.1 ⊗ₜ[k] x.2) (fun e => by
        rw [← TensorProduct.span_tmul_eq_top]
        congr 1
        ext t
        simp [eq_comm]), Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  refine ⟨PiTensorProduct.tprod k (fun h => match h with
    | .inl e => (x e).1
    | .inr e => (x e).2), ?_⟩
  rw [pairMap_tprod]

theorem pairMap_injective : Function.Injective (pairMap F) := by
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).2 (pairMap_surjective F)
  rw [finrank_piTensorProduct, finrank_piTensorProduct, Fintype.prod_sum_type,
    ← Finset.prod_mul_distrib]
  simp only [Module.finrank_tensorProduct]

/-- **Pairing the ends of every edge**: `⨂_e (A e ⊗ B e) ≃ ⨂_{h ∈ E ⊕ E} F h`. -/
noncomputable def pairEquiv :
    (⨂[k] e, (F (.inl e) ⊗[k] F (.inr e))) ≃ₗ[k] ⨂[k] h, F h :=
  (LinearEquiv.ofBijective (pairMap F) ⟨pairMap_injective F, pairMap_surjective F⟩).symm

theorem pairEquiv_symm_tprod (f : ∀ h, F h) :
    (pairEquiv F).symm (PiTensorProduct.tprod k f) =
      PiTensorProduct.tprod k (fun e => f (.inl e) ⊗ₜ[k] f (.inr e)) :=
  pairMap_tprod F f

/-- Pairing intertwines factorwise maps. -/
theorem pairEquiv_map (φ : ∀ h, F h →ₗ[k] F h) (t : ⨂[k] e, (F (.inl e) ⊗[k] F (.inr e))) :
    pairEquiv F (PiTensorProduct.map (fun e => TensorProduct.map (φ (.inl e)) (φ (.inr e))) t) =
      PiTensorProduct.map φ (pairEquiv F t) := by
  apply (pairEquiv F).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  obtain ⟨s, rfl⟩ := (pairEquiv F).symm.surjective t
  rw [LinearEquiv.apply_symm_apply]
  have : (pairEquiv F).symm.toLinearMap ∘ₗ PiTensorProduct.map φ =
      PiTensorProduct.map (fun e => TensorProduct.map (φ (.inl e)) (φ (.inr e))) ∘ₗ
        (pairEquiv F).symm.toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro f
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
      PiTensorProduct.map_tprod, LinearEquiv.coe_coe, pairEquiv_symm_tprod,
      TensorProduct.map_tmul]
  exact (LinearMap.congr_fun this s).symm

end Pairs

/-- A linear equivalence underlying an `FDRep` isomorphism is equivariant. -/
theorem isoToLinearEquiv_ρ {X Y : FDRep k G} (i : X ≅ Y) (g : G) (x : X) :
    FDRep.isoToLinearEquiv i (X.ρ g x) = Y.ρ g (FDRep.isoToLinearEquiv i x) := by
  rw [FDRep.Iso.conj_ρ i g, LinearEquiv.conj_apply]
  simp

/-- `PiTensorProduct.congr` intertwines factorwise maps that its components intertwine. -/
theorem piCongr_map {κ : Type*} {S T : κ → Type*} [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, AddCommGroup (T i)] [∀ i, Module k (T i)] (f : ∀ i, S i ≃ₗ[k] T i)
    (φ : ∀ i, S i →ₗ[k] S i) (χ : ∀ i, T i →ₗ[k] T i)
    (h : ∀ i x, f i (φ i x) = χ i (f i x)) (t : ⨂[k] i, S i) :
    PiTensorProduct.congr f (PiTensorProduct.map φ t) =
      PiTensorProduct.map χ (PiTensorProduct.congr f t) := by
  have : (PiTensorProduct.congr f).toLinearMap ∘ₗ PiTensorProduct.map φ =
      PiTensorProduct.map χ ∘ₗ (PiTensorProduct.congr f).toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
      PiTensorProduct.map_tprod, LinearEquiv.coe_coe, PiTensorProduct.congr_tprod, h]
  exact LinearMap.congr_fun this t

/-! ### The lattice reshuffle -/

section Reshuffle

variable {Vx E : Type*} [Fintype E] (Γ : OrientedGraph Vx E) (π : E → FDRep k G)

/-- The vertex of a half-edge: `inl e` is the source end of `e`, `inr e` its target end. -/
def endpoint : E ⊕ E → Vx
  | .inl e => Γ.src e
  | .inr e => Γ.tgt e

/-- The factor of a half-edge: `π e` at the source end, `(π e)ᘁ` at the target end (the
convention of `incident`). -/
noncomputable def halfFactor : E ⊕ E → FDRep k G
  | .inl e => π e
  | .inr e => (π e)ᘁ

/-- The link block `⊗_e (V_{π e} ⊗ V_{π e}*)`. -/
abbrev EdgeBlock (π : E → FDRep k G) : Type _ :=
  ⨂[k] e, ((π e : Type u) ⊗[k] (((π e)ᘁ : FDRep k G) : Type u))

/-- The gauge action of `Vx → G` on the link block: on the link `e` the copy at `src e` acts on
`V_{π e}` and the copy at `tgt e` acts on `V_{π e}*`. -/
noncomputable def edgeGauge : Representation k (Vx → G) (EdgeBlock π) where
  toFun g := PiTensorProduct.map fun e =>
    TensorProduct.map ((π e).ρ (g (Γ.src e))) ((π e)ᘁ.ρ (g (Γ.tgt e)))
  map_one' := by
    simp only [Pi.one_apply, map_one]
    rw [← PiTensorProduct.map_one]
    congr 1
    funext e
    exact TensorProduct.map_one
  map_mul' g h := by
    simp only [Pi.mul_apply, map_mul]
    rw [← PiTensorProduct.map_mul]
    congr 1
    funext e
    exact TensorProduct.map_mul _ _ _ _

omit [Fintype E] in
theorem edgeGauge_apply (g : Vx → G) :
    edgeGauge Γ π g = PiTensorProduct.map fun e =>
      TensorProduct.map ((π e).ρ (g (Γ.src e))) ((π e)ᘁ.ρ (g (Γ.tgt e))) := rfl

open scoped Classical in
/-- The half-edges at `v`, in the order of `incident`: outgoing links, then incoming links. -/
noncomputable def halfList (v : Vx) : List (E ⊕ E) :=
  ((Finset.univ.filter (fun e => Γ.src e = v)).toList.map Sum.inl) ++
    ((Finset.univ.filter (fun e => Γ.tgt e = v)).toList.map Sum.inr)

theorem mem_halfList (v : Vx) (h : E ⊕ E) : h ∈ halfList Γ v ↔ endpoint Γ h = v := by
  classical
  cases h <;> simp [halfList, endpoint]

theorem nodup_halfList (v : Vx) : (halfList Γ v).Nodup := by
  classical
  refine List.Nodup.append ((Finset.nodup_toList _).map Sum.inl_injective)
    ((Finset.nodup_toList _).map Sum.inr_injective) ?_
  intro a ha hb
  simp only [List.mem_map] at ha hb
  obtain ⟨_, -, rfl⟩ := ha
  obtain ⟨_, -, h⟩ := hb
  exact Sum.inr_ne_inl h

theorem halfList_map (v : Vx) :
    (halfList Γ v).map (halfFactor π) = (incident Γ π v).map HalfEdge.factor := by
  simp only [halfList, incident, List.map_append, List.map_map]
  rfl

theorem tensorList_halfList (v : Vx) :
    tensorList ((halfList Γ v).map (halfFactor π)) = vertexRep (incident Γ π v) := by
  rw [halfList_map]; rfl

/-- Reindex the fibre of `endpoint` over `v` by the list `halfList Γ v`. -/
noncomputable def fibreReindex (v : Vx) :
    (⨂[k] j : {h // endpoint Γ h = v}, halfFactor π j.1) ≃ₗ[k]
      ⨂[k] i : {h // h ∈ halfList Γ v}, halfFactor π i.1 :=
  PiTensorProduct.reindex k (fun j : {h // endpoint Γ h = v} => (halfFactor π j.1 : Type u))
    (Equiv.subtypeEquivRight (fun h => (mem_halfList Γ v h).symm))

theorem fibreReindex_tprod (v : Vx) (f : ∀ h, halfFactor π h) :
    fibreReindex Γ π v (PiTensorProduct.tprod k (fun j : {h // endpoint Γ h = v} => f j.1)) =
      PiTensorProduct.tprod k (fun i : {h // h ∈ halfList Γ v} => f i.1) :=
  PiTensorProduct.reindex_tprod _ _

theorem fibreReindex_map (v : Vx) (φ : ∀ h, halfFactor π h →ₗ[k] halfFactor π h)
    (t : ⨂[k] j : {h // endpoint Γ h = v}, halfFactor π j.1) :
    fibreReindex Γ π v (PiTensorProduct.map (fun j => φ j.1) t) =
      PiTensorProduct.map (fun i => φ i.1) (fibreReindex Γ π v t) :=
  (PiTensorProduct.map_reindex (fun j : {h // endpoint Γ h = v} => φ j.1) _ t).symm

/-- Identify the list tensor with the vertex space. -/
noncomputable def vertexCast (v : Vx) :
    tensorList ((halfList Γ v).map (halfFactor π)) ≃ₗ[k] VertexSpace Γ π v :=
  FDRep.isoToLinearEquiv (eqToIso (tensorList_halfList Γ π v))

open scoped Classical in
/-- **Per-vertex reshuffle**: the half-edges at `v` (indexed by the fibre of `endpoint`)
tensor to the vertex space `W_v = vertexRep (incident Γ π v)`. -/
noncomputable def vertexEquiv (v : Vx) :
    (⨂[k] j : {h // endpoint Γ h = v}, halfFactor π j.1) ≃ₗ[k] VertexSpace Γ π v :=
  (fibreReindex Γ π v).trans
    ((listEquiv (halfFactor π) (halfList Γ v) (nodup_halfList Γ v)).trans (vertexCast Γ π v))

theorem vertexEquiv_equivariant (v : Vx) (g : G)
    (t : ⨂[k] j : {h // endpoint Γ h = v}, halfFactor π j.1) :
    vertexEquiv Γ π v (PiTensorProduct.map (fun j => (halfFactor π j.1).ρ g) t) =
      (vertexRep (incident Γ π v)).ρ g (vertexEquiv Γ π v t) := by
  classical
  show vertexCast Γ π v (listEquiv (halfFactor π) (halfList Γ v) (nodup_halfList Γ v)
      (fibreReindex Γ π v (PiTensorProduct.map (fun j => (halfFactor π j.1).ρ g) t))) =
    (vertexRep (incident Γ π v)).ρ g (vertexCast Γ π v
      (listEquiv (halfFactor π) (halfList Γ v) (nodup_halfList Γ v) (fibreReindex Γ π v t)))
  rw [fibreReindex_map Γ π v (fun h => (halfFactor π h).ρ g), listEquiv_equivariant]
  exact isoToLinearEquiv_ρ _ g _

open scoped Classical in
/-- **The edge-to-vertex reshuffle** `⊗_e (V_{π e} ⊗ V_{π e}*) ≃ ⊗_v W_v(π)`: pair the ends of
every link, regroup the half-edges by their vertex, and tensor each vertex's half-edges in the
order of `incident`. -/
noncomputable def reshuffle [Fintype Vx] [DecidableEq Vx] :
    EdgeBlock π ≃ₗ[k] RegroupedBlock Γ π :=
  (pairEquiv (halfFactor π)).trans
    ((regroupEquiv (endpoint Γ) (fun h => (halfFactor π h : Type u))).trans
      (PiTensorProduct.congr (vertexEquiv Γ π)))

/-- **The reshuffle is gauge-equivariant**: it carries the link action `edgeGauge` (the copy
at `src e` on `V_{π e}`, the copy at `tgt e` on `V_{π e}*`) to the vertex action `blockGauge`
(the copy at `v` on `W_v(π)`). -/
theorem reshuffle_equivariant [Fintype Vx] [DecidableEq Vx] (g : Vx → G) (t : EdgeBlock π) :
    reshuffle Γ π (edgeGauge Γ π g t) = blockGauge Γ π g (reshuffle Γ π t) := by
  classical
  let φ : ∀ h, halfFactor π h →ₗ[k] halfFactor π h := fun h => (halfFactor π h).ρ (g (endpoint Γ h))
  have h1 : pairEquiv (halfFactor π) (edgeGauge Γ π g t) =
      PiTensorProduct.map φ (pairEquiv (halfFactor π) t) := pairEquiv_map (halfFactor π) φ t
  show PiTensorProduct.congr (vertexEquiv Γ π)
      (regroupEquiv (endpoint Γ) (fun h => (halfFactor π h : Type u))
        (pairEquiv (halfFactor π) (edgeGauge Γ π g t))) =
    PiTensorProduct.map (fun v => (vertexRep (incident Γ π v)).ρ (g v))
      (PiTensorProduct.congr (vertexEquiv Γ π)
        (regroupEquiv (endpoint Γ) (fun h => (halfFactor π h : Type u))
          (pairEquiv (halfFactor π) t)))
  rw [h1, regroupEquiv_map]
  have h2 : (fun v => PiTensorProduct.map (fun j : {h // endpoint Γ h = v} => φ j.1)) =
      fun v => PiTensorProduct.map (fun j : {h // endpoint Γ h = v} => (halfFactor π j.1).ρ (g v)) := by
    funext v
    congr 1
    funext j
    simp only [φ, j.2]
  rw [h2]
  exact piCongr_map _ _ _ (fun v x => vertexEquiv_equivariant Γ π v (g v) x) _

/-- The inverse reshuffle is gauge-equivariant too. -/
theorem reshuffle_symm_equivariant [Fintype Vx] [DecidableEq Vx] (g : Vx → G)
    (t : RegroupedBlock Γ π) :
    (reshuffle Γ π).symm (blockGauge Γ π g t) = edgeGauge Γ π g ((reshuffle Γ π).symm t) := by
  apply (reshuffle Γ π).injective
  rw [reshuffle_equivariant, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- The vectors at the two ends of every link, as a family over half-edges. -/
def halfVec (a : ∀ e, π e) (b : ∀ e, ((π e)ᘁ : FDRep k G)) : ∀ h, halfFactor π h
  | .inl e => a e
  | .inr e => b e

/-- **The reshuffle on pure tensors**: `⊗_e (a_e ⊗ b_e)` goes to the vertex tensor whose
`v`-th factor is the nested tensor of the `a_e` (links leaving `v`) and the `b_e` (links
entering `v`), in the order of `incident`. So `reshuffle` is the permutation of tensor
factors, not just some isomorphism. -/
theorem reshuffle_tprod [Fintype Vx] [DecidableEq Vx] (a : ∀ e, π e)
    (b : ∀ e, ((π e)ᘁ : FDRep k G)) :
    reshuffle Γ π (PiTensorProduct.tprod k (fun e => a e ⊗ₜ[k] b e)) =
      PiTensorProduct.tprod k (fun v => vertexCast Γ π v
        (listTmul (halfFactor π) (halfList Γ v) (fun i => halfVec π a b i.1))) := by
  classical
  have h1 : pairEquiv (halfFactor π) (PiTensorProduct.tprod k (fun e => a e ⊗ₜ[k] b e)) =
      PiTensorProduct.tprod k (halfVec π a b) := by
    apply (pairEquiv (halfFactor π)).symm.injective
    rw [LinearEquiv.symm_apply_apply, pairEquiv_symm_tprod]
    rfl
  show PiTensorProduct.congr (vertexEquiv Γ π)
      (regroupEquiv (endpoint Γ) (fun h => (halfFactor π h : Type u))
        (pairEquiv (halfFactor π) (PiTensorProduct.tprod k (fun e => a e ⊗ₜ[k] b e)))) = _
  rw [h1, regroupEquiv_tprod, PiTensorProduct.congr_tprod]
  congr 1
  funext v
  show vertexCast Γ π v (listEquiv (halfFactor π) (halfList Γ v) (nodup_halfList Γ v)
    (fibreReindex Γ π v (PiTensorProduct.tprod k (fun j => halfVec π a b j.1)))) = _
  rw [fibreReindex_tprod, listEquiv_tprod]

end Reshuffle

/-! ### Peter–Weyl per link implies the regrouped assumption -/

section Links

variable {Vx E : Type*} [Fintype E]

/-- **Named assumption (Peter–Weyl per link).** The lattice Hilbert space `H` decomposes over
labellings `π : E → Irr`: each block projection `proj π : H → ⊗_e (V_{π e} ⊗ V_{π e}*)` is
equivariant for the link action `edgeGauge`, and the blocks separate points. For
`G = SU(3)`, `k = ℂ`, `H = ⊗_e L²(SU(3))` this is the Peter–Weyl decomposition
`L²(G) = ⊕_π V_π ⊗ V_π*` applied link by link, with left translation at `src e` acting on `V`
and right translation at `tgt e` acting on `V*`. It does NOT contain the reshuffle, which is
proved (`reshuffle`, `reshuffle_equivariant`). -/
structure PeterWeylLinks (k : Type u) (G : Type v) [Field k] [Group G]
    (Γ : OrientedGraph Vx E) (Irr : Type*) (irr : Irr → FDRep k G)
    (H : Type*) [AddCommGroup H] [Module k H] (gauge : Representation k (Vx → G) H) where
  /-- The component of a state in the link block of the labelling `π`. -/
  proj : ∀ π : E → Irr, H →ₗ[k] EdgeBlock (irr ∘ π)
  /-- Gauge transformations act link by link. -/
  proj_equivariant : ∀ (π : E → Irr) (g : Vx → G) (ψ : H),
    proj π (gauge g ψ) = edgeGauge Γ (irr ∘ π) g (proj π ψ)
  /-- A state is determined by its components. -/
  proj_separating : ∀ ψ : H, (∀ π, proj π ψ = 0) → ψ = 0

/-- **Peter–Weyl per link implies the regrouped assumption**: composing each link projection
with the proved gauge-equivariant reshuffle gives `PeterWeylLattice`. -/
noncomputable def PeterWeylLinks.toLattice [Fintype Vx] [DecidableEq Vx]
    {Γ : OrientedGraph Vx E} {Irr : Type*} {irr : Irr → FDRep k G}
    {H : Type*} [AddCommGroup H] [Module k H] {gauge : Representation k (Vx → G) H}
    (PW : PeterWeylLinks k G Γ Irr irr H gauge) : PeterWeylLattice k G Γ Irr irr H gauge where
  proj π := (reshuffle Γ (irr ∘ π)).toLinearMap ∘ₗ PW.proj π
  proj_equivariant π g ψ := by
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      PW.proj_equivariant, reshuffle_equivariant]
  proj_separating ψ h := PW.proj_separating ψ fun π =>
    (reshuffle Γ (irr ∘ π)).map_eq_zero_iff.1 (h π)

theorem toLattice_proj_ne_zero [Fintype Vx] [DecidableEq Vx]
    {Γ : OrientedGraph Vx E} {Irr : Type*} {irr : Irr → FDRep k G}
    {H : Type*} [AddCommGroup H] [Module k H] {gauge : Representation k (Vx → G) H}
    (PW : PeterWeylLinks k G Γ Irr irr H gauge) (ψ : H) (π : E → Irr) (hπ : PW.proj π ψ ≠ 0) :
    PW.toLattice.proj π ψ ≠ 0 :=
  fun h => hπ ((reshuffle Γ (irr ∘ π)).map_eq_zero_iff.1 h)

/-- **Gauge support rule from Peter–Weyl per link.** Same conclusion as
`gauge_support_rule_regrouped`, assuming only `PeterWeylLinks` (the reshuffle is proved). -/
theorem gauge_support_rule_links [Fintype Vx] [DecidableEq Vx] {Γ : OrientedGraph Vx E}
    {Irr : Type*} {irr : Irr → FDRep k G} [∀ i, Simple (irr i)] {H : Type*} [AddCommGroup H]
    [Module k H] {gauge : Representation k (Vx → G) H} (PW : PeterWeylLinks k G Γ Irr irr H gauge)
    (ψ : H) (hψ : ∀ g, gauge g ψ = ψ) (π : E → Irr) (hπ : PW.proj π ψ ≠ 0) (v : Vx) :
    (∀ x, ntList (incident Γ (irr ∘ π) v) ≠ [x]) ∧
    (∀ x y, ntList (incident Γ (irr ∘ π) v) = [x, y] →
      (x.out = true → y.out = false → Nonempty (x.rep ≅ y.rep)) ∧
      (x.out = false → y.out = true → Nonempty (x.rep ≅ y.rep)) ∧
      (x.out = true → y.out = true → Nonempty (x.repᘁ ≅ y.rep)) ∧
      (x.out = false → y.out = false → Nonempty (x.rep ≅ y.repᘁ))) :=
  gauge_support_rule_regrouped PW.toLattice ψ hψ π (toLattice_proj_ne_zero PW ψ π hπ) v

/-- `PeterWeylLinks` for `SU(3)` over `ℂ`. -/
abbrev PeterWeylLinksSU3 (Γ : OrientedGraph Vx E) (Irr : Type*) (irr : Irr → FDRep ℂ SU3)
    (H : Type*) [AddCommGroup H] [Module ℂ H] (gauge : Representation ℂ (Vx → SU3) H) :=
  PeterWeylLinks ℂ SU3 Γ Irr irr H gauge

/-- **`gauge_support_rule_links` for `SU(3)`**, under `PeterWeylLinksSU3`. -/
theorem gauge_support_rule_links_SU3 [Fintype Vx] [DecidableEq Vx] {Γ : OrientedGraph Vx E}
    {Irr : Type*} {irr : Irr → FDRep ℂ SU3} [∀ i, Simple (irr i)] {H : Type*} [AddCommGroup H]
    [Module ℂ H] {gauge : Representation ℂ (Vx → SU3) H}
    (PW : PeterWeylLinksSU3 Γ Irr irr H gauge)
    (ψ : H) (hψ : ∀ g, gauge g ψ = ψ) (π : E → Irr) (hπ : PW.proj π ψ ≠ 0) (v : Vx) :
    (∀ x, ntList (incident Γ (irr ∘ π) v) ≠ [x]) ∧
    (∀ x y, ntList (incident Γ (irr ∘ π) v) = [x, y] →
      (x.out = true → y.out = false → Nonempty (x.rep ≅ y.rep)) ∧
      (x.out = false → y.out = true → Nonempty (x.rep ≅ y.rep)) ∧
      (x.out = true → y.out = true → Nonempty (x.repᘁ ≅ y.rep)) ∧
      (x.out = false → y.out = false → Nonempty (x.rep ≅ y.repᘁ))) :=
  gauge_support_rule_links PW ψ hψ π hπ v

/-- The link block-sum model with the blockwise link action. -/
noncomputable def piEdgeGauge (Γ : OrientedGraph Vx E) (Irr : Type*) (irr : Irr → FDRep k G) :
    Representation k (Vx → G) (∀ π : E → Irr, EdgeBlock (irr ∘ π)) where
  toFun g := LinearMap.pi fun π => edgeGauge Γ (irr ∘ π) g ∘ₗ LinearMap.proj π
  map_one' := LinearMap.ext fun ψ => funext fun π => by
    simp only [map_one, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      Module.End.one_apply]
  map_mul' g h := LinearMap.ext fun ψ => funext fun π => by
    simp only [map_mul, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      Module.End.mul_apply]

/-- **Consistency of `PeterWeylLinks`**: the link block-sum model satisfies it. -/
noncomputable def PeterWeylLinks.model (Γ : OrientedGraph Vx E) (Irr : Type*)
    (irr : Irr → FDRep k G) :
    PeterWeylLinks k G Γ Irr irr (∀ π : E → Irr, EdgeBlock (irr ∘ π)) (piEdgeGauge Γ Irr irr) where
  proj π := LinearMap.proj π
  proj_equivariant _ _ _ := rfl
  proj_separating _ h := funext h

end Links
end GaugeSupport

#print axioms GaugeSupport.listEquiv_tprod
#print axioms GaugeSupport.listEquiv_equivariant
#print axioms GaugeSupport.regroupEquiv_map
#print axioms GaugeSupport.pairEquiv_map
#print axioms GaugeSupport.vertexEquiv_equivariant
#print axioms GaugeSupport.reshuffle_equivariant
#print axioms GaugeSupport.reshuffle_symm_equivariant
#print axioms GaugeSupport.reshuffle_tprod
#print axioms GaugeSupport.PeterWeylLinks.toLattice
#print axioms GaugeSupport.gauge_support_rule_links
#print axioms GaugeSupport.gauge_support_rule_links_SU3
