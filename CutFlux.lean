import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import CutBound

/-!
# Cut flux from Gauss's law (Spectrum, 2026-11-11)

`CutBound` assumes each cut carries nonzero triality. This file derives that from
triality conservation at every vertex (the Gauss law mod the centre `ℤ/3`).

* `sum_div_eq_fluxOut`: summing the vertex divergences over a region `S` gives the net
  triality flux out of `S` (discrete divergence theorem, any finite directed multigraph).
* `fluxOut_eq_zero`: under Gauss's law the flux out of every region is `0` mod 3.
* `cut_flux_eq`: two signed cuts that differ by the boundary of a region carry the same flux.
* `ring_triality_const`: on a periodic ring every link carries the same triality.
* `ring_cut_bound`: in a sector of nonzero triality every link of an `L`-link ring is a
  nonzero-triality cut, so `CutBound.cut_bound` gives cost `≥ 4·L` (`C₂ ≥ (4/3)·L`).

Input still assumed: that triality is conserved at each vertex (the divergence
hypothesis). `ThetaTriality.singlet_triality` proves it for trivalent singlet vertices;
for a general vertex it is the centre acting by `ω^triality` on an invariant.
-/

namespace CutFlux

open Finset

variable {n m : ℕ}

/-- A finite directed multigraph: link `e` runs from `src e` to `tgt e`. -/
structure DGraph (n m : ℕ) where
  src : Fin m → Fin n
  tgt : Fin m → Fin n

/-- Net triality leaving vertex `v`. -/
def div (G : DGraph n m) (t : Fin m → ZMod 3) (v : Fin n) : ZMod 3 :=
  ∑ e, ((if G.src e = v then t e else 0) - (if G.tgt e = v then t e else 0))

/-- Net triality flux out of the region `S`. -/
def fluxOut (G : DGraph n m) (t : Fin m → ZMod 3) (S : Finset (Fin n)) : ZMod 3 :=
  ∑ e, ((if G.src e ∈ S then t e else 0) - (if G.tgt e ∈ S then t e else 0))

/-- Discrete divergence theorem. -/
theorem sum_div_eq_fluxOut (G : DGraph n m) (t : Fin m → ZMod 3) (S : Finset (Fin n)) :
    ∑ v ∈ S, div G t v = fluxOut G t S := by
  unfold div fluxOut
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]

/-- Gauss's law at every vertex forces zero flux out of every region. -/
theorem fluxOut_eq_zero (G : DGraph n m) (t : Fin m → ZMod 3)
    (gauss : ∀ v, div G t v = 0) (S : Finset (Fin n)) : fluxOut G t S = 0 := by
  rw [← sum_div_eq_fluxOut]
  exact Finset.sum_eq_zero fun v _ => gauss v

/-- Flux through a signed cut `c` (coefficient `c e` on link `e`). -/
def cutFlux (t c : Fin m → ZMod 3) : ZMod 3 := ∑ e, t e * c e

/-- Two signed cuts that differ by the boundary of a region carry the same flux. -/
theorem cut_flux_eq (G : DGraph n m) (t : Fin m → ZMod 3) (gauss : ∀ v, div G t v = 0)
    (S : Finset (Fin n)) (c₁ c₂ : Fin m → ZMod 3)
    (hbd : ∀ e, c₁ e - c₂ e =
      (if G.src e ∈ S then 1 else 0) - (if G.tgt e ∈ S then 1 else 0)) :
    cutFlux t c₁ = cutFlux t c₂ := by
  have h0 := fluxOut_eq_zero G t gauss S
  have key : cutFlux t c₁ - cutFlux t c₂ = fluxOut G t S := by
    unfold cutFlux fluxOut
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← mul_sub, hbd e]
    split_ifs <;> ring
  exact sub_eq_zero.mp (key.trans h0)

/-- The periodic ring with `L + 1` sites: link `i` runs from site `i` to site `i + 1`. -/
def ring (L : ℕ) : DGraph (L + 1) (L + 1) where
  src := fun e => e
  tgt := fun e => e + 1

theorem ring_div (L : ℕ) (t : Fin (L + 1) → ZMod 3) (v : Fin (L + 1)) :
    div (ring L) t v = t v - t (v - 1) := by
  unfold div ring
  simp only
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ v t]
  have : ∀ e : Fin (L + 1), (e + 1 = v) ↔ (e = v - 1) := fun e =>
    ⟨fun h => by rw [← h]; simp, fun h => by rw [h]; simp⟩
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]

open Fin.NatCast in
/-- On a periodic ring, Gauss's law makes every link carry the same triality. -/
theorem ring_triality_const (L : ℕ) (t : Fin (L + 1) → ZMod 3)
    (gauss : ∀ v, div (ring L) t v = 0) (e : Fin (L + 1)) : t e = t 0 := by
  have step : ∀ v : Fin (L + 1), t v = t (v - 1) := fun v => by
    have := gauss v
    rw [ring_div] at this
    exact sub_eq_zero.mp this
  have hk : ∀ k : ℕ, t (k : Fin (L + 1)) = t 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [step ((k + 1 : ℕ) : Fin (L + 1))]
      simpa using ih
  simpa using hk e.val

/-- Triality as an element of `ℤ/3`. -/
def tri (x : ThetaFloor.Irrep) : ZMod 3 := (ThetaTriality.triality x : ZMod 3)

theorem tri_ne_zero {x : ThetaFloor.Irrep} (h : tri x ≠ 0) : ThetaTriality.triality x ≠ 0 := by
  intro h0; apply h; simp [tri, h0]

/-- Ring cut bound: on an `(L+1)`-link periodic ring with triality conserved at every
site, a sector of nonzero triality costs at least `4·(L+1)` in `cas3` units, i.e.
`C₂ ≥ (4/3)·(L+1)`. The nonzero-triality-per-cut hypothesis of `CutBound` is derived. -/
theorem ring_cut_bound (L : ℕ) (x : Fin (L + 1) → ThetaFloor.Irrep)
    (gauss : ∀ v, div (ring L) (fun e => tri (x e)) v = 0)
    (sector : tri (x 0) ≠ 0) :
    4 * (L + 1) ≤ ((List.finRange (L + 1)).map (fun e => ThetaFloor.cas3 (x e))).sum := by
  have hall : ∀ e, tri (x e) ≠ 0 := fun e => by
    rw [ring_triality_const L (fun e => tri (x e)) gauss e]; exact sector
  have h := CutBound.cut_bound ((List.finRange (L + 1)).map x)
    (fun y hy => by
      obtain ⟨e, -, rfl⟩ := List.mem_map.mp hy
      exact tri_ne_zero (hall e))
  simpa [List.map_map, Function.comp_def] using h

end CutFlux
