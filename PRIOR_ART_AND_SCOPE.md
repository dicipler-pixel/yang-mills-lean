# How to describe the spectral certificate

The demonstrated comparison is on the **same SU(3) single-loop operator**:
at `λ/κ=100`, the scalar-norm estimate gives an inconclusive lower
quantity of approximately `−33.3376`, while keeping the retained boundary
matrix gives the rational full-character-space gap bound `1936077/100000`.
The code bounds the entire omitted representation tail analytically and
checks the retained signs by outward exact arithmetic. The five later
original-link spatial models use an energy-resolved boundary comparison and
have separate fixed-cell targets.

The general idea of recovering full-operator spectral information from a
finite reduction predates this work. Dusson, Sigal and Stamm,
[“The Feshbach-Schur map and perturbation theory”](https://arxiv.org/html/2105.02058v1),
Theorems 1.1–1.2 and equation (1.9), give full-operator eigenvalue bounds
and an isospectral finite reduction under their hypotheses. We therefore
credit the Schur/Feshbach framework as prior mathematics and locate the
contribution in the concrete SU(3) character boundary, rational certificate
and structured-versus-scalar comparison.

Gauge simulation work also need not stop at the truncated spectrum. For
example, Ciavarella et al.,
[“Truncation uncertainties for accurate quantum simulations of lattice gauge theories”](https://arxiv.org/html/2508.00061v4),
use a U(1) single plaquette as the motivating gauge example and explicitly
relate full and truncated eigenenergies in Section 2.1; the paper develops
truncation and dynamics estimates beyond that example. Its task and
hypotheses are different from an exact-arithmetic SU(3) gap certificate.
No matched computational benchmark or general superiority claim follows
from this repository's scalar-control result.

The useful claim for an abstract is:

> We give reproducible exact-arithmetic gap certificates for an untruncated
> SU(3) single-loop Hamiltonian by combining character-space boundary
> structure, an analytic infinite-tail bound and Schur-complement inertia.
> The boundary-sensitive estimate succeeds where our scalar coupling
> estimate fails. The spatial extension provides exact fixed-cell
> certificates; quantitative moderate-coupling volume control remains open.

This is a bounded positioning check, not an exhaustive priority survey.
It does not identify the paper's classical frame with a quantum path-integral
measure, infer first-order holonomy response in general, or make a
four-dimensional mass-gap claim.
