# Certified window-wall cells (round five)

`WindowWallCells.lean` (repository root) checks in Lean the certified numbers behind the window wall:
for each graph at the first tested coupling where the wall closes, `28/3 ≤ Σ c_p L_p` by exact
arithmetic, and through `WindowWallFinite.no_window` no certificate of the C ≤ 8 complete-tail class
exists there for any retained fraction s in (0, 1].

| Graph | Faces | lambda/alpha | Margin Σ c_p L_p − 28/3 |
|---|---:|---:|---:|
| Two squares | 2 | 8 | 1.4512 |
| Three-square strip | 3 | 5 | 0.1241 |
| Three-face corner | 3 | 5 | 0.4204 |
| Cube | 6 | 3 | 2.0306 |
| Two adjacent cubes | 11 | 2 | 2.5889 |

Inputs taken as hypotheses in Lean: the certified endpoints (`hlo`, `hhi`, from the integer-interval
inertia checks in `window_wall_endpoints_03.py`, 2^-192 grid, one-loop cutoff N = 30, h = 1/1000),
concavity of each one-loop ground energy in kappa, and `d − r ≤ W(s)` (LOCAL_ENERGY_FLOORS.md).
alpha = 1, even allocation only. Not a gap statement.

How it was made: the ten statements were frozen first (`WindowWallCells_Statements.lean`); two
provers wrote proofs by different routes; both compiled on this repository's CI (trial branch
`claude/cells-trial`, run 42948500894). The library keeps the one that calls
`WindowWallFinite.no_window`; the independent per-face route (`plaquette_secant` + `linarith`) is kept
here as `WindowWallCells_m2_second_proof.lean.txt`. The only change after freezing was marking the
rational data `noncomputable` (real division), applied identically to both.

False control: `FalseControls/WindowWallCellsControl.lean` claims the strip clears 28/3 by 1/8; its
true margin is 0.12407, so it must be rejected.
