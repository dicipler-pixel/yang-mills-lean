# Ky Fan chord: standalone certificate, plus the B189 constant 5/8 (Grey, 2026-11-11)

Jeromie Beasley research programme. Credit: Grey (colour team).
Not on main: local branch only. No Lean file is changed.

## What this is
The open-questions ledger v2, item 3, said the float Ky Fan chord (open_tests_05 T2) "is not a certified bound yet". It
needed certified endpoint values and a Rayleigh–Ritz upper bound in place of the exact E0. Green's `../kyfan_chord/`
already does both, using the repo's interval-inertia code. This folder adds a **self-contained certificate file plus an
independent verifier**. It uses only the Python standard library, and every accept/reject decision is made in exact
rationals or in outward-rounded integer intervals. Floats only propose the numbers.

Model: one SU(3) plaquette, `H(κ) = κ C2 + 8 (3 − Re χ_(1,0))` on class functions (the whole gauge-invariant space),
character basis. Chord variable κ, interval [1/2, 2], covered by 6 chords with nodes every 1/4.

## Run
```
python3 kyfan_cert.py              # verify certificate.json and run the 9 controls (~30 s, stdlib only)
python3 kyfan_cert.py --generate   # re-propose certificate.json with NumPy, then verify (~2.5 min)
python3 b189_five_eighths.py       # B189: exact derivation of c = 5/8 (SymPy), plus a float cross-check (~4 min)
```
Outputs: `kyfan_cert.out`, `b189_five_eighths.out`.

## What is certified (and how)
1. **Endpoint/node values.** At each node κ, `H − z` is split into the block p+q ≤ 32 and its tail. The tail satisfies
   `D ≥ κ·d`, where d = min C2 on level 33: C2 is diagonal and V ≥ 0 is a multiplication operator. So the Schur
   complement is ≥ `K(z) = A − z − (64/4)·M/(κd − z)`, where M is the boundary overlap matrix (computed, not assumed).
   An LDL of K(z) in integer intervals on a 2⁻²²⁴ grid with outward rounding, where no pivot interval contains 0, gives
   #neg(H − z) ≤ #neg(K). 0 negatives means E0 ≥ z0, and at most 1 means E1 ≥ z1 (Haynsworth + Sylvester).
   As an independent cross-check, the repo's `su3_character_certificate.interval_inertia` gives the same counts at κ = 1
   (0, 1, and 1, 2 for the +1/1000 shifts).

   | κ | E0 ∈ (certified) | E1 ≥ |
   |---|---|---|
   | 1/2 | [7.2852763892, 7.2852763893] | 10.9533417670 |
   | 3/4 | [8.7234838307, 8.7234838308] | 13.1166679293 |
   | 1 | [9.8782825003, 9.8782825004] | 14.8511858925 |
   | 5/4 | [10.8516438290, 10.8516438291] | 16.3099859780 |
   | 3/2 | [11.6958782311, 11.6958782312] | 17.5715620253 |
   | 7/4 | [12.4420664536, 12.4420664537] | 18.6825013655 |
   | 2 | [13.1104618443, 13.1104618444] | 19.6731226411 |

   The exact rationals are in `certificate.json`.
2. **E0 upper bound = Rayleigh–Ritz.** There are 25 finite-support rational trial vectors (denominator 10¹²), tuned at
   κ = 1/2 + j/16. Their exact quotients are `E0(κ) ≤ α_i κ + β_i` for every κ (variational principle in the full
   space). The verifier recomputes each (α_i, β_i) from the vector and rejects any stored line that does not match.
3. **Chord.** S = E0 + E1 is concave in κ (Ky Fan: an infimum of affine functions; this is the named hypothesis of
   `KyFanChord.chord_gap_lower_inf`). On each piece, gap ≥ chord(S_lo) − 2·min_i(α_i κ + β_i). That bound is convex
   piecewise linear, and its exact minimum is taken over all vertices.

**Result:** gap(κ) ≥ **366806537/100000000 = 3.66806537 for every κ ∈ [1/2, 2]** (λ = 8). The exact rational minimum
of the bound is ≈ 3.6680653776, attained at κ = 1/2. A 2-vector Rayleigh–Ritz bound gives E1(1/2) ≤ 10.9533417771, so
gap(1/2) ≤ 3.6680653879. The uniform bound is therefore within 1.0e-8 of the true minimum gap.
Per piece: [1/2,3/4] ≥ 3.66806537 · [3/4,1] ≥ 4.39318409 · [1,5/4] ≥ 4.97290339 · [5/4,3/2] ≥ 5.45834214 ·
[3/2,7/4] ≥ 5.87568379 · [7/4,2] ≥ 6.24043491.

## Controls (all 9 must be rejected; all are)
- E0 lower bound +1/1000 at κ = 1/2 and κ = 2: the negative count rises to ≥ 1.
- E1 lower bound +1/1000 at κ = 1/2 and κ = 2: the negative count rises to ≥ 2.
- Certificate with z0(1/2) raised by 1/1000: the verifier rejects it.
- Certificate with a Rayleigh line lowered by 1/1000: the verifier rejects it (the line no longer matches its vector).
- E0 upper bound lowered by 1/1000 at every node: refuted, because it falls below the certified E0 lower bound.
- Uniform gap bound raised by 1/1000: refuted by the certified gap(1/2) upper bound.
- Piece-0 claim raised by 1/1000: the verifier rejects it.

## B189: the constant 5/8 (`b189_five_eighths.py`)
Claim: gap(1, μ) = 2√μ − 5/8 + O(μ^(−1/2)) for one SU(3) plaquette, so gap(κ, λ) = 2√(κλ) − (5/8)κ + O(κ^(3/2)/√λ).
- **Exact reduction (checked).** Weyl's character formula turns H on class functions into
  `−½ Δ_plane − 1 + μ Σ_j (1 − cos φ_j)` acting on Weyl-antisymmetric functions on the torus. The checks are
  C2(p,q) = |k⊥|²/2 − 1 for p, q < 30, and 2 Re tr U · χ_pq = the sum of the six neighbours.
  The −|ρ|² = −1 is the only curvature term, and it cancels in the gap.
- **Harmonic part.** ω = √μ. The lowest antisymmetric states are Δ(φ)e^(−ωr²/2) (energy 4ω) and Δ(φ)(4 − ωr²)e^(−ωr²/2)
  (6ω, the only sign-representation state at that level). This gives the leading 2√μ.
- **First anharmonic order.** −(μ/24)Σφ_j⁴. Exact Gaussian integrals give ⟨Σφ⁴⟩₀ = 10/μ and ⟨Σφ⁴⟩₁ = 25/μ, so
  **c = (μ/24)(25 − 10)/μ = 5/8 exactly**. Also E0 = 4√μ − 17/12 + O(μ^(−1/2)) and E1 = 6√μ − 49/24 + O(μ^(−1/2)).
- **Float cross-check.** √μ·(c(μ) − 5/8) = 0.144, 0.139, 0.137, 0.136 at μ = 64, 256, 1024, 4096. This is the
  expected O(μ^(−1/2)) remainder. Control: a doubled quartic weight gives 5/4, which is rejected.
- **Status.** 5/8 is now an exact, derived first-order coefficient, no longer just a fit. Its validity as an asymptotic
  statement rests on the standard harmonic-approximation / semiclassical expansion for a non-degenerate potential
  minimum (Simon 1983; Helffer–Sjöstrand), which is cited here, not re-proved. The potential has a unique minimum at
  U = 1. A fully rigorous two-sided O(μ^(−1/2)) error bound is **not** done here.

## Still open
- The Ky Fan concavity is still a named hypothesis in Lean. The numbers above are not imported into Lean.
- This certificate covers one plaquette at λ = 8 only. The two-square cell at large λ is still limited by the 19-state
  node floors (see `../kyfan_chord/README.md`). That needs the exact SU(3) recoupling basis.
- Finite systems only. There is no continuum claim, and no continuum mass gap is claimed.
