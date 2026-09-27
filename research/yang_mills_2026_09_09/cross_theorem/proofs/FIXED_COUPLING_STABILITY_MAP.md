# Fixed-spacing strong-coupling uniformity: an application of Yarotsky

Jeromie N. Beasley research programme — 9 September 2026.

**Attribution and scope.** This is a hypothesis-by-hypothesis application of
D. A. Yarotsky, *Ground states in relatively bounded quantum perturbations of
classical lattice systems*, arXiv:math-ph/0412040v1, Theorem1, published in
Communications in Mathematical Physics261(2006),799–819. It is not a new
stability theorem or a numerical threshold at lambda/alpha=1. The primary
statement explicitly allows infinite-dimensional on-site spaces and gives a
volume-independent gap for sufficiently small finite-range perturbations.

Primary source: https://arxiv.org/html/math-ph/0412040v1

## Exact Hilbert space and classical terms

Consider periodic cubic spatial lattices of side L>=3 and the full link space
L²(SU(3)^E). Package the three positively oriented links starting at each site x
into an on-site Hilbert space H_x=L²(SU(3)) tensor³. The constant function Omega_x
is a distinguished normalized vector. Put k_x=sum_(i=1)^3 C_(x,i).
The k_x are diagonal in the Peter–Weyl product basis, have a unique zero vector
Omega_x, and are at least4/3 on its orthogonal complement.

Take Lambda0={0,e1,e2,e3}, and define

    h_x=(3/4) sum_(y in x+Lambda0) k_y.

Every h_x is classical, is zero on the unique product vacuum of its whole
four-site support, and is at least1 on the complement. This checks the local
nondegeneracy hypothesis on the whole patch—not on one factor extended by
spectator identities. Since each site belongs to four translated patches,

    sum_x h_x=3 sum_x k_x.

The stated infinite-dimensional partition-of-unity condition follows from the
Peter–Weyl electric spectral decomposition. These unbounded positive operators
are handled as closed quadratic forms, as in the cited theorem.

## Bounded local perturbation and normalization

Let V_p=3-ReTr U_p. Its range is [0,9/2]. At each x the three plaquettes based at
x, in the (1,2),(1,3),(2,3) planes, have link variables supported within
x+Lambda0. Write rho=lambda/alpha>=0 and center their sum:

    phi_x=3rho [sum_(i<j) V_(x,i,j) - (27/4) I].

The three-term sum lies between0 and27/2; thus

    ||phi_x|| <= (81/4)rho.

The total normalized operator is

    sum_x(h_x+phi_x)=(3/alpha)H - (81rho/4)|Lambda| I,
    H=alpha sum_e C_e + lambda sum_p V_p.

The scalar shift changes no gap. The perturbation has relative form bound zero
and absolute form constant beta=(81/4)rho. It is translation invariant, symmetric
and bounded, with precisely the same fixed finite support as h_x.

## Consequence of the established theorem

Yarotsky's Theorem1 supplies positive admissible constants depending only on the
dimension and the fixed support. Let beta_* be such an absolute constant. For
sufficiently small fixed rho, for example any rho with (81/4)rho<=beta_*, the
normalized finite-volume operators have a unique ground state and a positive
gap gamma independent of the periodic volume. Consequently

    gap(H_L) >= alpha gamma/3, independently of L.

The theorem also supplies a thermodynamic ground-state limit and clustering
for this regime. No numerical value of beta_* or gamma is obtained here. In
particular the argument does not certify that rho=1, or any displayed moderate-
coupling cube target, lies in this perturbative regime.

At every finite volume the full compact configuration-space Schrödinger
operator has a strictly positive unique ground state by positivity improvement.
Gauge invariance and uniqueness make that ground state gauge invariant.
Restriction to the physical invariant Hilbert space keeps the ground and cannot
create a lower first excitation. The same lower gap bound therefore applies to
the finite-volume physical subspace. This does not assume a common interacting
local vacuum or frustration-freeness of the Kogut–Susskind sum.

## What remains outside this application

This corrects an overly broad statement that all spatial uniformity is missing:
qualitative fixed-spacing strong-coupling uniformity is covered by established
stability theory. The present quantitative moderate-coupling certificates,
control along a weak-coupling continuum trajectory, nontrivial four-dimensional
field construction and required quantum-field axioms are different tasks.
The native eye reports missing uniformity for its quantitative finite-cell
certificates; that report should be read with this regime distinction.

The previously executed spatial_stability_checks.py verifies the finite periodic
incidences and normalization arithmetic. Those finite checks are not a proof of
Yarotsky's theorem. The all-volume application above uses the primary theorem
and its explicit hypotheses, not extrapolation from five lattice sizes.
