import Mathlib
-- False: one split's own retained floor is not ≥ the equal-split value P·g(c)
-- (g = min(·,1), two faces, κ = (0, 2), E = 2, c = 1).
example : (2:ℝ) * min 1 1 ≤ min 0 1 + min 2 1 := by norm_num
