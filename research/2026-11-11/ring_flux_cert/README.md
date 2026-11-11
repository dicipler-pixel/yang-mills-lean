# SU(3) periodic ring: certified gap and flux floor at strong coupling (λ ≤ 1)

Green, 2026-11-11, built on main `3422e89`. Jeromie N. Beasley ([ORCID](https://orcid.org/0009-0006-4645-5643)) · GitHub dicipler-pixel · X @d1c1pler · YouTube [@AtlasMemoriae](https://www.youtube.com/@AtlasMemoriae) · [Atlas Memoriae](https://atlas-memoriae.dicipler.workers.dev)

**Scope.** These are rigorous bounds, but only at strong coupling (λ ≤ 1). They say nothing about weak coupling. The real test starts around λ ≈ 2 and is not covered here.

Hamiltonian: H = Σ C₂ + λ Σ_p (3 − Re tr U_p), on the SU(3) periodic ring of L plaquettes, in units of g²/2.

## Result

| Ring | λ | gap ≥ (triality 0) | flux floor in (triality 1 − triality 0) | ink float (gap / floor) |
|---|---|---|---|---|
| L=2 | 1/4 | 5.20904 | [2.66465, 2.66467] | 5.209 / 2.665 |
| L=2 | 1/2 | 5.09287 | [2.65801, 2.65804] | 5.094 / 2.658 |
| L=2 | 1 | 4.88708 | [2.62735, 2.62761] | 4.898 / 2.629 |
| L=3 | 1/4 | 5.21246 | [3.99901, 3.99905] | 5.213 / 3.999 |
| L=3 | 1/2 | 5.10054 | [3.99550, 3.99557] | 5.101 / 3.996 |
| L=3 | 1 | 4.90193 | [3.97555, 3.97696] | 4.920 / 3.978 |

The gap and the flux floor each have their own certificate. The gap is E₁ − E₀ inside the triality-0 sector. The floor is E₀(triality 1) − E₀(triality 0), bounded from both sides.

## Method (`cert.py`)

- **Lower bounds.** An exact Schur/Feshbach form bound is used, K(z) = A_PP − z G_PP − λ² C/(d − z). If #neg K(z) ≤ k, then the sector has at most k eigenvalues below z. The negative count is certified by a float congruence with a-priori rounding bounds and Gershgorin discs separated from 0, using Sylvester's law of inertia. It reuses the repo's `su3_character_certificate.py` unchanged.
- **Hidden floor d.** This comes from the total-energy cap of 18 and is worked out **separately for each triality sector**. In each sector, d = m_Q(θ) + 2θL·e0_lo(λ/2θ), where e0_lo is a certified one-plaquette ground-energy bound. Every floor clears the level it protects.
- **Upper bounds.** These are exact rational Rayleigh quotients of rational trial vectors.
- **Controls.** At every certified level, raising z by 1/1000 makes the count go up, so the certificate is rejected as expected. Every sector also passes the exact symmetry checks with defect (0, 0, 0) and an intertwiner-count cross-check.

Reproduce with `OMP_NUM_THREADS=1 python run_cert.py L 18 18` for L = 2 or 3. The outputs are `ring_L{2,3}.out/.json`, and the logs are in `runs/`.

## Credit

ink between the stars supplied the periodic-box set-up, the total-energy cap of 18, and the float reference values in the last column. Green did the certification.
