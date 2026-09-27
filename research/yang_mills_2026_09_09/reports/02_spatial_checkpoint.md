# Checkpoint 2 — local-window proof and coupled SU(3) tests

9 September 2026. The proof `proofs/LOCAL_WINDOW_AND_GAP_TRANSFER.md` gives a relative single-link hidden floor, a recursive low-energy-subspace tail bound, and a gap transfer using local boundary support. It does not assume an already established full mass gap. It remains a written proof, not a Lean operator theorem or a continuum construction.

The standard-library budget calculator passed 316 exact arithmetic checks and rejected six malformed inputs. At alpha=lambda=omega=1, error budget 1/10, the first passing single-link shell cutoffs are N=12 for 81 links, N=13 for 3,000 links, and N=15 for 3,000,000 links. These are evaluations of sufficient bounds, NOT large-lattice diagonalizations. The one-link Peter–Weyl dimensions are respectively 2,012,920; 3,436,720; 9,093,096. A small shell index does not make the full many-link problem computationally small.

Independent finite numerical checks passed 1,857 assertions over 96 finite U(1)-rotor analogue configurations and 100 complex dense projection examples. All 100 deliberately false zero-leakage claims failed. The tests cover the local trial comparison, relative hidden floor, spectral-window operator norm, global projection norm, local cross-form estimate, Rayleigh–Ritz comparison, and gap-transfer case distinction. This analogue is not an SU(3) large-lattice experiment.

The complete shared-link SU(3) cutoff has also been enlarged from 7 to 15 and 19 gauge states. With alpha=1, the 19-state exact full-tail lower bounds include 4.908928 at lambda=1, 4.273698 at lambda=2, 2.466778 at lambda=3, and 0.991383 at lambda=4. Lambda=5,6,8,10,20 produced no feasible certificate in the specified allocation sweep; no gaplessness follows.

A separate differential implementation using all eight Gell-Mann generators verifies all 19 electric eigenfunctions on 24 Haar-sampled pairs, maximum residual 2.14e-14. Treating the plaquettes as independent instead produces an error exceeding 4.24 on the rectangle control. Independent sampled Haar integration with 100,000 SU(3) pairs agrees with the exact Gram, potential and squared-potential matrices within the declared diagnostic tolerances. This numerical integration is not the exact certificate.

The first isolated Lean build failed on six elaboration/reduction issues. The failure log was downloaded and preserved. Explicit finite index cases and rational normalization have been committed; the replacement build is being checked separately. Root CI success is not being substituted for this new module's acceptance.

Scripts, complete rational witnesses and raw reports will be committed with the self-contained result package. No existing draft or main-branch manuscript is changed.
