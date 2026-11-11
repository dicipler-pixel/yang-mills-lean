import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import WindowWallFinite

/-!
  Split-free window wall (Red's two-halves Jensen bound).

  P faces, an allocation κ_p ≥ 0 with Σ_p κ_p ≤ E, equal share c = E / |P|, and
  g concave and nondecreasing on [0, ∞).
  (1) Excited side:  Σ_p g((1−s)κ_p) ≤ |P|·g((1−s)c)            (Jensen + monotonicity).
  (2) Retained side: if r ≥ Σ_p g(κ'_p) for every allocation κ' with Σ κ' ≤ E
      (the operator-splitting fact, a hypothesis), then r ≥ |P|·g(c).
  (3) Combined: d ≤ s·T + Σ_p g((1−s)κ_p) gives
      d − r ≤ s·T − |P|·(g(c) − g((1−s)c)), independent of κ (T = 28/3 in the paper).
  So the equal-split wall of `WindowWallFinite` excludes every split at once.
  Physics inputs taken as hypotheses: concavity and monotonicity of g in κ, the
  excited-side bound on d, and the operator-splitting bound on r.
-/

namespace WindowWallJensen

open Set

/-- Excited side: Σ_p g((1−s)κ_p) ≤ |P|·g((1−s)·E/|P|) for any allocation with Σ κ ≤ E. -/
theorem excited_le {ι : Type*} (P : Finset ι) (g : ℝ → ℝ) (hg : ConcaveOn ℝ (Ici 0) g)
    (hmono : MonotoneOn g (Ici 0)) (κ : ι → ℝ) (hκ : ∀ p ∈ P, 0 ≤ κ p) {E s : ℝ}
    (hE : ∑ p ∈ P, κ p ≤ E) (hs1 : s ≤ 1) :
    ∑ p ∈ P, g ((1 - s) * κ p) ≤ P.card * g ((1 - s) * (E / P.card)) := by
  rcases P.eq_empty_or_nonempty with rfl | hne
  · simp
  have hn : (0:ℝ) < P.card := by exact_mod_cast hne.card_pos
  have h1s : 0 ≤ 1 - s := by linarith
  have hK : 0 ≤ ∑ p ∈ P, κ p := Finset.sum_nonneg hκ
  have J := hg.le_map_sum (t := P) (w := fun _ => 1 / (P.card : ℝ))
    (p := fun q => (1 - s) * κ q) (fun _ _ => by positivity)
    (by rw [Finset.sum_const, nsmul_eq_mul]; field_simp)
    (fun q hq => mem_Ici.mpr (mul_nonneg h1s (hκ q hq)))
  simp only [smul_eq_mul] at J
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at J
  have hlo : 1 / (P.card : ℝ) * ((1 - s) * ∑ p ∈ P, κ p) ∈ Ici (0:ℝ) :=
    mem_Ici.mpr (by positivity)
  have hhi : (1 - s) * (E / P.card) ∈ Ici (0:ℝ) :=
    mem_Ici.mpr (mul_nonneg h1s (div_nonneg (le_trans hK hE) hn.le))
  have hle : 1 / (P.card : ℝ) * ((1 - s) * ∑ p ∈ P, κ p) ≤ (1 - s) * (E / P.card) := by
    rw [one_div_mul_eq_div, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hE hn.le) h1s
  have hm := hmono hlo hhi hle
  have key : ∑ p ∈ P, g ((1 - s) * κ p)
      = P.card * (1 / (P.card : ℝ) * ∑ p ∈ P, g ((1 - s) * κ p)) := by
    field_simp
  rw [key]
  exact mul_le_mul_of_nonneg_left (le_trans J hm) hn.le

/-- Retained side: the operator-splitting floor at the equal allocation gives r ≥ |P|·g(E/|P|). -/
theorem retained_ge {ι : Type*} (P : Finset ι) (g : ℝ → ℝ) {E r : ℝ} (hE : 0 ≤ E)
    (hr : ∀ κ' : ι → ℝ, (∀ p ∈ P, 0 ≤ κ' p) → ∑ p ∈ P, κ' p ≤ E →
      ∑ p ∈ P, g (κ' p) ≤ r) :
    P.card * g (E / P.card) ≤ r := by
  have h := hr (fun _ => E / P.card) (fun _ _ => div_nonneg hE (Nat.cast_nonneg _)) (by
    rw [Finset.sum_const, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos P.card with h0 | hpos
    · simp [h0, hE]
    · have : (0:ℝ) < P.card := by exact_mod_cast hpos
      rw [mul_div_cancel₀ _ this.ne'])
  simpa [Finset.sum_const, nsmul_eq_mul] using h

/-- Split-free bound: d − r ≤ s·T − |P|·(g(c) − g((1−s)c)) with c = E/|P|, for every split κ. -/
theorem split_free {ι : Type*} (P : Finset ι) (g : ℝ → ℝ) (hg : ConcaveOn ℝ (Ici 0) g)
    (hmono : MonotoneOn g (Ici 0)) (κ : ι → ℝ) (hκ : ∀ p ∈ P, 0 ≤ κ p) {E s T d r : ℝ}
    (hE : ∑ p ∈ P, κ p ≤ E) (hs1 : s ≤ 1)
    (hd : d ≤ s * T + ∑ p ∈ P, g ((1 - s) * κ p))
    (hr : ∀ κ' : ι → ℝ, (∀ p ∈ P, 0 ≤ κ' p) → ∑ p ∈ P, κ' p ≤ E →
      ∑ p ∈ P, g (κ' p) ≤ r) :
    d - r ≤ s * T - P.card * (g (E / P.card) - g ((1 - s) * (E / P.card))) := by
  have hx := excited_le P g hg hmono κ hκ hE hs1
  have hR := retained_ge P g (le_trans (Finset.sum_nonneg hκ) hE) hr
  nlinarith

/-- The paper's form, T = 28/3. -/
theorem split_free_28_3 {ι : Type*} (P : Finset ι) (g : ℝ → ℝ) (hg : ConcaveOn ℝ (Ici 0) g)
    (hmono : MonotoneOn g (Ici 0)) (κ : ι → ℝ) (hκ : ∀ p ∈ P, 0 ≤ κ p) {E s d r : ℝ}
    (hE : ∑ p ∈ P, κ p ≤ E) (hs1 : s ≤ 1)
    (hd : d ≤ s * (28 / 3) + ∑ p ∈ P, g ((1 - s) * κ p))
    (hr : ∀ κ' : ι → ℝ, (∀ p ∈ P, 0 ≤ κ' p) → ∑ p ∈ P, κ' p ≤ E →
      ∑ p ∈ P, g (κ' p) ≤ r) :
    d - r ≤ s * (28 / 3) - P.card * (g (E / P.card) - g ((1 - s) * (E / P.card))) :=
  split_free P g hg hmono κ hκ hE hs1 hd hr

/-- No window for any split: a certified equal-split secant with T ≤ E·L gives d − r ≤ 0. -/
theorem no_window_split_free {ι : Type*} (P : Finset ι) (hP : P.Nonempty) (g : ℝ → ℝ)
    (hg : ConcaveOn ℝ (Ici 0) g) (hmono : MonotoneOn g (Ici 0)) (κ : ι → ℝ)
    (hκ : ∀ p ∈ P, 0 ≤ κ p) {E s T d r h L : ℝ} (hEpos : 0 < E)
    (hE : ∑ p ∈ P, κ p ≤ E) (hh : 0 < h)
    (hL : L * h ≤ g (E / P.card + h) - g (E / P.card)) (hT : T ≤ E * L)
    (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hd : d ≤ s * T + ∑ p ∈ P, g ((1 - s) * κ p))
    (hr : ∀ κ' : ι → ℝ, (∀ p ∈ P, 0 ≤ κ' p) → ∑ p ∈ P, κ' p ≤ E →
      ∑ p ∈ P, g (κ' p) ≤ r) :
    d - r ≤ 0 := by
  have hn : (0:ℝ) < P.card := by exact_mod_cast hP.card_pos
  have hsf := split_free P g hg hmono κ hκ hE hs1 hd hr
  have hc : 0 < E / P.card := div_pos hEpos hn
  have hsumL : ∑ _p ∈ P, E / P.card * L = E * L := by
    rw [Finset.sum_const, nsmul_eq_mul]; field_simp
  have hsumW : ∑ _p ∈ P, (g (E / P.card) - g ((1 - s) * (E / P.card)))
      = P.card * (g (E / P.card) - g ((1 - s) * (E / P.card))) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  exact WindowWallFinite.no_window P (fun _ => g) (fun _ _ => hg) (fun _ => E / P.card)
    (fun _ => h) (fun _ => L) (fun _ _ => hc) (fun _ _ => hh) (fun _ _ => hL) T
    (by rw [hsumL]; exact hT) hs0 hs1 (by rw [hsumW]; exact hsf)

/-- False control: without monotonicity the excited side fails
    (g = −x, one face, E = 1, κ = 0, s = 0: g(0) = 0 > 1·g(1) = −1). -/
theorem excited_needs_monotone :
    ¬ ((fun x : ℝ => -x) ((1 - 0) * 0) ≤ 1 * (fun x : ℝ => -x) ((1 - 0) * (1 / 1))) := by
  norm_num

end WindowWallJensen
