import WindowWallCells
-- Deliberately false: the strip at lambda/alpha = 5 clears 28/3 by 0.12407, not by 1/8.
example : (28 : ℝ) / 3 + 1 / 8 ≤ ∑ p : Fin 3, WindowWallCells.stripC p *
    ((WindowWallCells.stripLo p - WindowWallCells.stripHi p) / (1 / 1000)) := by
  norm_num [Fin.sum_univ_three, WindowWallCells.stripC, WindowWallCells.stripLo,
    WindowWallCells.stripHi]
