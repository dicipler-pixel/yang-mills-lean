# Checkpoint 1 — recovered sources and fresh reruns

9 September 2026. These runs were executed in a fresh working copy; recovered originals were preserved unchanged.

## Recovered archives

- `Yang_Mills_Continuation_2026-09-08.zip`: SHA-256 `3bd8f6872700931c6a22d2d8fa296b3579e56d9be37df5e3892140dfe6744f2a`.
- `Yang_Mills_Restart_2026-09-08.zip`: SHA-256 `0aec04e5881cbf6c863a2b300aa6ddf931b163feef8e4a6734fb19f10d6459c6`.
- `Elemental_Peeling_Combined_Complete.zip`: SHA-256 `4f3b96184a2124c2716b368972f32184cf2c6ed3d9a6832dc32ed8a3dc32e617` (recovered for selected cross-track checks, not yet rerun).

All entries in the continuation's packaged SHA256SUMS.txt matched. The uploaded continuation PDF and the recovered bundled PDF have different bytes but identical page-by-page extracted text (11 pages; 20,714 extracted characters). This is text agreement, not a claim of binary identity or full visual identity.

## Executed results

`python -S su3/su3_character_certificate.py` exited 0. Acceptance uses only the standard library's exact integer/fraction arithmetic. It reproduced 13,587 structural/arithmetic assertions, 20 inertia certificates, and 2,275 strictly signed pivots.

| lambda/kappa | N | retained dimension | certified full one-plaquette gap/kappa |
|---|---:|---:|---:|
| 0 | 1 | 3 | 4/3 analytically |
| 1/10 | 3 | 10 | 1.2868372 |
| 1 | 6 | 28 | 1.3401688 |
| 10 | 10 | 66 | 5.6481431 |
| 100 | 25 | 351 | 19.36077 |

The last scalar norm certificate remains -33.3376126530834 (inconclusive). The matrix-support certificate succeeds. Spectral recheck elapsed 1.754 seconds within this runtime; not a general speed benchmark.

`python verify_restart.py --output results_reproduced.json` exited 0: 2,723 checks passed. The earlier continuation had inherited this count without rerunning it; this checkpoint actually recovers and reruns that script.

`python frame/verify_frame.py` exited 0: 67 rational controls and 411 numerical comparisons; largest absolute Frobenius residual 8.3993e-15.

`python holonomy/verify_holonomy.py` exited 0: all 24 exact symbolic checks, including instanton curvature, anti-self-duality, charge integral and the nonconstant contractible-loop trace.

No fresh Lean compilation or continuum mass-gap result is claimed by these reruns.

## Next investigations, not results yet

1. Exact Haar integration for a two-plaquette SU(3) graph sharing one link. The physical low-electric-energy subspace must be complete, rather than a tensor product of independent plaquette characters silently omitting allowed gauge states.
2. A hypothesis-by-hypothesis application of established local perturbation theory to the full link Hilbert space of a spatial lattice. This can address fixed-spacing strong-coupling volume uniformity; it cannot be extrapolated to the weak-coupling continuum trajectory.
3. Energy-resolved hidden-sector bounds and the obstruction caused by discarding extensive spectator ground energy.

The repository main branch and existing research drafts are unchanged.
