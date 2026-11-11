import WindowWallFinite

/-!
  Window wall, the certified cells (round five).

  For each graph below, at the first tested coupling where the window wall closes, the data
  are exact rationals from `research/window_wall_2026_11_10/window_wall_endpoints_03.py`:
  `c p` is the face's allocation coefficient, `lo p` a certified lower bound for the one-loop
  ground energy at `c p + 1/1000`, `hi p` a certified upper bound at `c p`. The bounds come from
  the repository's integer-interval inertia checks (Python, 2^-192 grid); here they are
  hypotheses `hlo`, `hhi`. Concavity of each ground energy in kappa is a hypothesis.
  The `_sum` theorems check `28/3 ≤ Σ c p * L p` by exact arithmetic; the `_no_window` theorems
  feed that into `WindowWallFinite.no_window`: no certificate of the C ≤ 8 complete-tail class
  exists for that graph at that coupling, for any retained fraction s in (0, 1].
  alpha = 1, even allocation only. Not a gap statement.
-/

namespace WindowWallCells

open Set

/-! ## Two squares sharing one link, lambda/alpha = 8 (2 faces) -/

/-- Allocation coefficients. -/
noncomputable def twoC : Fin 2 → ℝ := ![7/2, 7/2]

/-- Certified lower bounds for the ground energy at `c p + 1/1000`. -/
noncomputable def twoLo : Fin 2 → ℝ := ![
    3213886872609/200000000000,
    3213886872609/200000000000]

/-- Certified upper bounds for the ground energy at `c p`. -/
noncomputable def twoHi : Fin 2 → ℝ := ![
    32135787439/2000000000,
    32135787439/2000000000]

theorem two_eight_sum :
    (28 : ℝ) / 3 ≤ ∑ p : Fin 2, twoC p * ((twoLo p - twoHi p) / (1 / 1000)) := by
  sorry

theorem two_eight_no_window (g : Fin 2 → ℝ → ℝ) (hg : ∀ p, ConcaveOn ℝ (Ici 0) (g p))
    (hlo : ∀ p, twoLo p ≤ g p (twoC p + 1 / 1000)) (hhi : ∀ p, g p (twoC p) ≤ twoHi p)
    {d r s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hdr : d - r ≤ s * (28 / 3) - ∑ p : Fin 2, (g p (twoC p) - g p ((1 - s) * twoC p))) :
    d - r ≤ 0 := by
  sorry

/-! ## Strip of three squares, lambda/alpha = 5 (3 faces) -/

/-- Allocation coefficients. -/
noncomputable def stripC : Fin 3 → ℝ := ![7/2, 3, 7/2]

/-- Certified lower bounds for the ground energy at `c p + 1/1000`. -/
noncomputable def stripLo : Fin 3 → ℝ := ![
    11586026658303/1000000000000,
    1109547789021/100000000000,
    11586026658303/1000000000000]

/-- Certified upper bounds for the ground energy at `c p`. -/
noncomputable def stripHi : Fin 3 → ℝ := ![
    23170280133/2000000000,
    11094394137/1000000000,
    23170280133/2000000000]

theorem strip_five_sum :
    (28 : ℝ) / 3 ≤ ∑ p : Fin 3, stripC p * ((stripLo p - stripHi p) / (1 / 1000)) := by
  sorry

theorem strip_five_no_window (g : Fin 3 → ℝ → ℝ) (hg : ∀ p, ConcaveOn ℝ (Ici 0) (g p))
    (hlo : ∀ p, stripLo p ≤ g p (stripC p + 1 / 1000)) (hhi : ∀ p, g p (stripC p) ≤ stripHi p)
    {d r s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hdr : d - r ≤ s * (28 / 3) - ∑ p : Fin 3, (g p (stripC p) - g p ((1 - s) * stripC p))) :
    d - r ≤ 0 := by
  sorry

/-! ## Three faces at an open cubic corner, lambda/alpha = 5 (3 faces) -/

/-- Allocation coefficients. -/
noncomputable def cornerC : Fin 3 → ℝ := ![3, 3, 3]

/-- Certified lower bounds for the ground energy at `c p + 1/1000`. -/
noncomputable def cornerLo : Fin 3 → ℝ := ![
    1109547789021/100000000000,
    1109547789021/100000000000,
    1109547789021/100000000000]

/-- Certified upper bounds for the ground energy at `c p`. -/
noncomputable def cornerHi : Fin 3 → ℝ := ![
    11094394137/1000000000,
    11094394137/1000000000,
    11094394137/1000000000]

theorem corner_five_sum :
    (28 : ℝ) / 3 ≤ ∑ p : Fin 3, cornerC p * ((cornerLo p - cornerHi p) / (1 / 1000)) := by
  sorry

theorem corner_five_no_window (g : Fin 3 → ℝ → ℝ) (hg : ∀ p, ConcaveOn ℝ (Ici 0) (g p))
    (hlo : ∀ p, cornerLo p ≤ g p (cornerC p + 1 / 1000)) (hhi : ∀ p, g p (cornerC p) ≤ cornerHi p)
    {d r s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hdr : d - r ≤ s * (28 / 3) - ∑ p : Fin 3, (g p (cornerC p) - g p ((1 - s) * cornerC p))) :
    d - r ≤ 0 := by
  sorry

/-! ## One open cube, lambda/alpha = 3 (6 faces) -/

/-- Allocation coefficients. -/
noncomputable def cubeC : Fin 6 → ℝ := ![2, 2, 2, 2, 2, 2]

/-- Certified lower bounds for the ground energy at `c p + 1/1000`. -/
noncomputable def cubeLo : Fin 6 → ℝ := ![
    1715089049967/250000000000,
    1715089049967/250000000000,
    1715089049967/250000000000,
    1715089049967/250000000000,
    1715089049967/250000000000,
    1715089049967/250000000000]

/-- Certified upper bounds for the ground energy at `c p`. -/
noncomputable def cubeHi : Fin 6 → ℝ := ![
    1714852301/250000000,
    1714852301/250000000,
    1714852301/250000000,
    1714852301/250000000,
    1714852301/250000000,
    1714852301/250000000]

theorem cube_three_sum :
    (28 : ℝ) / 3 ≤ ∑ p : Fin 6, cubeC p * ((cubeLo p - cubeHi p) / (1 / 1000)) := by
  sorry

theorem cube_three_no_window (g : Fin 6 → ℝ → ℝ) (hg : ∀ p, ConcaveOn ℝ (Ici 0) (g p))
    (hlo : ∀ p, cubeLo p ≤ g p (cubeC p + 1 / 1000)) (hhi : ∀ p, g p (cubeC p) ≤ cubeHi p)
    {d r s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hdr : d - r ≤ s * (28 / 3) - ∑ p : Fin 6, (g p (cubeC p) - g p ((1 - s) * cubeC p))) :
    d - r ≤ 0 := by
  sorry

/-! ## Two adjacent open cubes, lambda/alpha = 2 (11 faces) -/

/-- Allocation coefficients. -/
noncomputable def twoCubesC : Fin 11 → ℝ := ![2, 11/6, 11/6, 11/6, 11/6, 4/3, 11/6, 11/6, 11/6, 11/6, 2]

/-- Certified lower bounds for the ground energy at `c p + 1/1000`. -/
noncomputable def twoCubesLo : Fin 11 → ℝ := ![
    5040216354753/1000000000000,
    14847453604541/3000000000000,
    14847453604541/3000000000000,
    14847453604541/3000000000000,
    14847453604541/3000000000000,
    3430414750901/750000000000,
    14847453604541/3000000000000,
    14847453604541/3000000000000,
    14847453604541/3000000000000,
    14847453604541/3000000000000,
    5040216354753/1000000000000]

/-- Certified upper bounds for the ground energy at `c p`. -/
noncomputable def twoCubesHi : Fin 11 → ℝ := ![
    1259927319/250000000,
    618570337/125000000,
    618570337/125000000,
    618570337/125000000,
    618570337/125000000,
    1714852301/375000000,
    618570337/125000000,
    618570337/125000000,
    618570337/125000000,
    618570337/125000000,
    1259927319/250000000]

theorem twoCubes_two_sum :
    (28 : ℝ) / 3 ≤ ∑ p : Fin 11, twoCubesC p * ((twoCubesLo p - twoCubesHi p) / (1 / 1000)) := by
  sorry

theorem twoCubes_two_no_window (g : Fin 11 → ℝ → ℝ) (hg : ∀ p, ConcaveOn ℝ (Ici 0) (g p))
    (hlo : ∀ p, twoCubesLo p ≤ g p (twoCubesC p + 1 / 1000)) (hhi : ∀ p, g p (twoCubesC p) ≤ twoCubesHi p)
    {d r s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hdr : d - r ≤ s * (28 / 3) - ∑ p : Fin 11, (g p (twoCubesC p) - g p ((1 - s) * twoCubesC p))) :
    d - r ≤ 0 := by
  sorry

end WindowWallCells
