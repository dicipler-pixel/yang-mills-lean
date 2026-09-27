# Yang-Mills continuation - 8 September 2026

Start with `YANG_MILLS_CONTINUATION.pdf` or its Markdown source. This continuation proves local classical geometric statements and complete-tail spectral certificates for a gauge-invariant one-plaquette SU(3) quantum Hamiltonian. It does not prove the four-dimensional quantum Yang-Mills continuum mass gap. There is no fresh Lean certificate.

## What is included

- `YANG_MILLS_CONTINUATION.pdf` and `.md`: combined paper.
- `frame/LOCAL_FRAME.md`, `verify_frame.py`, `frame_results.json`: general local connection frame and checks.
- `holonomy/HYPERSURFACE_AUDIT.md`, `verify_holonomy.py`, `holonomy_results.json`: corrections, Wilson-loop counterexample, weighted-frame instanton and exact checks.
- `gap_review/GAUGE_CUTOFF_GAP_THEOREM.md`: domain-level Schur proof, gauge-compatible cutoff, fixed-lattice convergence and scale conditions.
- `su3/SU3_SINGLE_LOOP_CERTIFICATE.md`: detailed model and spectral proof.
- `su3/su3_character_certificate.py`: complete exact verifier, standard library only by default.
- `su3/certificate_targets.json`: rational targets proposed by numerical calculation, then independently certified.
- `su3/interval_pivot_witnesses.json`: all exact outward interval pivot enclosures.
- `su3/su3_results.json`: rational bounds and the actual run's summary.
- `sources/`: unchanged copies of the four uploaded handoffs, with provenance recorded in `sources/PROVENANCE.json`.
- `SHA256SUMS.txt`: final packaged-file hashes. Rerunning scripts rewrites result files, including elapsed time; that is expected to change their hashes.

## Recheck the exact SU(3) spectral certificates

From this extracted directory, run:

```text
python -S su3/su3_character_certificate.py
```

This needs only Python 3's standard library. It has been run with site packages disabled. No network, experiment, repository or numerical eigensolver is needed to accept the supplied rational targets. It should complete in seconds on a typical desktop. The certificate arithmetic uses unbounded integers, exact fractions and outward fixed-grid interval arithmetic, not fixed-width floating-point acceptance.

## Recheck all geometry and spectral outputs

If needed, install the listed dependencies once, then run the complete scripts:

```text
python -m pip install -r requirements.txt
python run_all.py
```

NumPy/SciPy are used for the numerical implementation controls of the general frame; SymPy is used for exact holonomy/instanton calculations. The geometric checks are separate from the exact standard-library spectral verifier.

To propose and certify new default spectral targets with SciPy, use:

```text
python su3/su3_character_certificate.py --generate
```

The default targets remain included for independent reproducibility. Numerical proposals are never themselves acceptance certificates. A pivot interval containing zero makes verification stop rather than silently accept a sign.

## Rebuild the PDF

The Markdown is the source of truth for the combined paper. With Pandoc and a LaTeX installation:

```text
pandoc YANG_MILLS_CONTINUATION.md --pdf-engine=xelatex -o YANG_MILLS_CONTINUATION.pdf
```

## Status boundaries

The finite-lattice cutoff theorem applies to a full finite spatial gauge lattice, but the executed numerical/certificate example is one plaquette. Representation labels are taken to infinity by a proven tail estimate. Spatial volume and continuum limits have not been taken. The energies in the certificate table are in units of kappa and are not physical masses in GeV.

The instanton is an established classical BPST/ADHM solution integrated into the graph-frame programme, not a new instanton or a quantum mass-gap proof. General universal connections and Schur/min-max methods are also established mathematics; the paper identifies what was explicitly constructed and checked in this continuation.

Only the four supplied handoffs were recovered as primary user source files here. Their old repository/source-reading claims are preserved as reported provenance, not upgraded to fresh readings. Nothing was published to GitHub or Zenodo.
