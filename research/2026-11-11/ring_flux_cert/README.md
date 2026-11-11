# SU(3) periodic ring: certified gap and flux floor, λ from 1/4 to 3

Green, 2026-11-11, built on main `3422e89`. Jeromie N. Beasley ([ORCID](https://orcid.org/0009-0006-4645-5643)) · GitHub dicipler-pixel · X @d1c1pler · YouTube [@AtlasMemoriae](https://www.youtube.com/@AtlasMemoriae) · [Atlas Memoriae](https://atlas-memoriae.dicipler.workers.dev)

**Scope.** These are rigorous bounds for two small finite rings (L = 2, 3) at fixed coupling values. The λ ≤ 1 rows are strong coupling. The λ = 3/2 to 3 rows reach the crossover region but are still finite-ring, fixed-λ results. They say nothing about weak coupling, the continuum, or a volume-uniform gap.

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

## Extension to λ = 3/2 … 3 (same method, same controls)

| Ring | cap | λ | gap ≥ (triality 0) | flux floor in | float in P (gap / floor) |
|---|---|---|---|---|---|
| L=2 | 18 | 3/2 | 4.70995 | [2.56830, 2.57169] | 4.753 / 2.571 |
| L=2 | 18 | 2 | 4.51275 | [2.47243, 2.49670] | 4.686 / 2.491 |
| L=2 | 18 | 5/2 | 4.13380 | [2.30857, 2.42734] | 4.692 / 2.398 |
| L=2 | 18 | 3 | 3.34915 | [1.94805, 2.41917] | 4.723 / 2.306 |
| L=3 | 18 | 3/2 | 4.68774 | [3.91738, 3.93825] | 4.821 / 3.935 |
| L=3 | 18 | 2 | 4.14096 | [3.68208, 3.89512] | 4.810 / 3.870 |
| L=3 | 22 | 2 | 4.61532 | [3.82763, 3.85716] | 4.719 / 3.855 |
| L=3 | 22 | 5/2 | 4.11825 | [3.55115, 3.77279] | 4.772 / 3.754 |
| L=3 | 22 | 3 | 2.59635 | [2.40103, 3.77372] | 4.924 / 3.652 |

At L=3 the cap-18 bounds loosen from λ = 5/2 (the hidden floor gets close to the protected levels), so L=3 is raised to cap 22 (`runs/L3_c22.log`, `lam2/ring_L3_cap22.*`). At λ = 3 even cap 22 is loose (gap ≥ 2.596 against float 4.924); a higher cap is needed to tighten it. As λ grows, the lower bounds drift away from the float values; that is the cap binding, not a sign the gap closes.

Reproduce: `OMP_NUM_THREADS=1 LAMS=3/2,2,5/2,3 python run_cert.py L 18 18` (outputs copied to `lam2/`), and `LAMS=2,5/2,3 python run_cert.py 3 22 22`. With `LAMS` unset the driver runs the original λ = 1/4, 1/2, 1.

## Method (`cert.py`)

- **Lower bounds.** An exact Schur/Feshbach form bound is used, K(z) = A_PP − z G_PP − λ² C/(d − z). If #neg K(z) ≤ k, then the sector has at most k eigenvalues below z. The negative count is certified by a float congruence with a-priori rounding bounds and Gershgorin discs separated from 0, using Sylvester's law of inertia. It reuses the repo's `su3_character_certificate.py` unchanged.
- **Hidden floor d.** This comes from the total-energy cap (18, or 22 where marked) and is worked out **separately for each triality sector**. In each sector, d = m_Q(θ) + 2θL·e0_lo(λ/2θ), where e0_lo is a certified one-plaquette ground-energy bound. Every floor clears the level it protects.
- **Upper bounds.** These are exact rational Rayleigh quotients of rational trial vectors.
- **Controls.** At every certified level, raising z by 1/1000 makes the count go up, so the certificate is rejected as expected. Every sector also passes the exact symmetry checks with defect (0, 0, 0) and an intertwiner-count cross-check.

Reproduce with `OMP_NUM_THREADS=1 python run_cert.py L 18 18` for L = 2 or 3. The outputs are `ring_L{2,3}.out/.json`, and the logs are in `runs/`.

## Credit

ink between the stars supplied the periodic-box set-up, the total-energy cap of 18, and the float reference values in the last column. Green did the certification.
