# Source/sink electric floor on the strip, corner and cube (Grey, 2026-11-10)

`strip_string.py` -> `strip_string.out`. Script by Grey.

A source (+1 triality) at u and a sink (-1) at v must be joined by a fundamental electric
string, so the electric floor is (g^2/2)(4/3) d, where d is the graph distance between u and v.
The script checks that the minimal fundamental support length equals d for every pair
(strip 28 pairs, corner 21, cube 28: 0 mismatches).

Scope: this is the strong-coupling end only. The magnetic term is untested.

Run from this folder with `python3 strip_string.py` (override the research path with
`YM_RESEARCH`). The output is byte-identical to running Grey's original.
