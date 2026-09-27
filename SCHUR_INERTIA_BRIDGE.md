# From a finite boundary certificate to a full fixed-lattice excitation gap

This is the exact scope of the September 8 written Schur-inertia argument, with
the later energy-resolved comparison made explicit. It is a fixed-operator
criterion. The Lean sign-transfer module below covers two finite steps, while
the operator-domain and negative-index transfer remain written mathematics.

Let `H = [[A,B],[B†,D]]` act on `ℂ^m ⊕ 𝒦`, where `m` is finite,
`A=A†`, `D=D† ≥ dI`, and `B` is bounded. The domain is
`ℂ^m ⊕ Dom(D)`. For real `z<d`, put

```text
R(z) = (D-z)⁻¹,
S(z) = A-z-B R(z) B†.
```

`R(z)` is bounded, positive and maps into `Dom(D)`. The bounded
invertible triangular change of variables with lower-left block `R(z)B†`
preserves the operator domain and gives a congruence between `H-z` and
`diag(S(z),D-z)`. Thus their negative quadratic-form indices and kernel
dimensions agree. Since `D-z>0`, the index below `z` belongs entirely to
the finite matrix `S(z)`. Invertibility of `S(z)` also puts `z` in the
resolvent of `H`.

Suppose a rigorously established Hermitian matrix comparison satisfies
`K(z) ≤ S(z) ≤ A-z`. A rational LDLᵀ factorization of `K(z)`, with
one strictly negative pivot and all other pivots strictly positive, exhibits
an `(m-1)`-dimensional positive subspace for `K(z)`. Loewner order carries
that *same subspace* to `S(z)`. A trial vector on which `A-z` is
strictly negative remains negative for `S(z)`. These `m` independent
sign directions show that `S(z)` is nonsingular and has exactly one negative
direction. Consequently the full `H` has one simple eigenvalue below
`z` and no spectrum at `z`. If a variational trial gives `E₀≤r<z`,
the vacuum-excluded spectral gap obeys `Δ≥z-r>0`. The exact vacuum vector
need not be known.

The original complete-tail bound takes `D≥dI` and `BB†≤M`, yielding
`K_M(z)=A-z-M/(d-z)≤S(z)`. The stronger spatial comparison uses positive
boundary matrices `M_e` and an *entire hidden-space* floor
`D≥s C_Q+E_* I`:

```text
K_res(z) = A-z-λ² Σ_e M_e/(s e+E_*-z).
```

The inequality `K_floor(z)≤K_res(z)≤S(z)` uses the full hidden floor,
including states invisible to `B†`; an estimate only on reached boundary
states is insufficient. Every denominator must be positive. The energy
labels describe a comparison for the electric operator, not the spectrum of
the interacting `D`. The five finite spatial instances and their exact
targets appear in the [spatial report](research/yang_mills_2026_09_09/cross_theorem/REPORT.md).
The complete single-loop proof and rational interval witnesses appear in
the [September 8 bundle](paper/2026-09-08/).

## Formalization boundary

The public Lean library checks the finite block congruence and positivity
floor transfer. [`SchurInertiaComparison.lean`](SchurInertiaComparison.lean)
also proves that Loewner order retains any certified positive trial subspace
and any negative upper-comparison trial vector. Its source does not yet
encode Sylvester's exact negative-index count, infinite self-adjoint operator
domains, or the full physical `K_res≤S(z)` hypothesis. The spatial
calculation has a separate complete-cutoff written proof and executable
checks, and no quantitative growing-volume margin at the displayed
couplings follows from these finite results.

The original paper's interval certificate can be replayed with
`python -S paper/2026-09-08/su3/su3_character_certificate.py`.
The later original-link models can be rebuilt from
`research/yang_mills_2026_09_09/cross_theorem/native/` with
`python -S recheck.py --out fresh_evidence`.
