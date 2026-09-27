# Local plaquette energy allocation without a common local vacuum

Jeromie N. Beasley research programme — new reconstruction,9September2026.

## One weighted cycle, including its non-gauge-invariant sectors

Let a simple cycle have link coefficients a_e>0, holonomy U_p, and

    h_p=sum_{e in p}a_e C_e+lambda_p(3-ReTrU_p), lambda_p>=0.

This acts on the full L² of its cycle-link configurations. Its kinetic part is
elliptic on a compact connected manifold and its potential is bounded and real.
The heat semigroup is positivity improving (the elliptic heat kernel is strictly
positive, and bounded real multiplication preserves that property by the
Feynman–Kac formula). Compact resolvent gives a unique strictly positive ground
state. The operator commutes with every vertex gauge transformation; uniqueness
makes that ground state gauge invariant. Thus its lowest full-space energy
is equal to its lowest gauge-invariant energy, although its entire excited
spectrum is not being identified with the class-function spectrum.

Gauge fixing a tree of the cycle leaves one holonomy, modulo conjugation.
On its class functions every link Casimir acts as the same holonomy Casimir.
The restricted Hamiltonian is therefore

    kappa_p C2+lambda_p(3-Re chi_(1,0)), kappa_p=sum_{e in p}a_e.

A certified lower bound e_p for this one-plaquette ground energy is a lower
bound for h_p on the WHOLE cycle-link Hilbert space. Extending h_p by spectator
identities preserves h_p>=e_p I. Its extended ground need not be unique; no
uniqueness assertion about the spectators is needed.

## Allocation on an overlapping plaquette graph

Let H=sum_e alpha_e C_e+sum_p lambda_p(3-ReTrU_p), alpha_e>0. Choose retained
coefficients beta_e>0 and positive allocation weights a_pe for each incidence
such that beta_e+sum_{p containing e}a_pe<=alpha_e. The leftover electric terms
are positive. Applying the preceding local result to each plaquette gives

    H >= sum_e beta_e C_e + E_*, E_*=sum_p e_p.            (1)

No two h_p are assumed to commute. No common local ground state is assumed.
This is an addition of quadratic-form inequalities, NOT frustration-free gap
gluing. Each e_p is an absolute local ground-energy lower bound, not a gap.

For equal alpha=1 and a common retained fraction0<s<1, a simple choice is
beta_e=s and a_pe=(1-s)/r_e, where r_e is the number of incident plaquettes.
Then kappa_p=(1-s)sum_{e in p}1/r_e. In particular:

- two squares sharing one link: kappa_p=(7/2)(1-s), both p;
- three-square strip: end coefficients(7/2)(1-s), middle3(1-s);
- three mutually adjacent corner faces: all3(1-s);
- six faces of a complete cube: all2(1-s).

The number7/2 is thus3exclusive edges plus half of1shared edge, not a fitted
constant or a change from seven physical links to eight independent ones.
For general common alpha multiply all these kappas by alpha.

## Compression and the complete omitted floor

Let P=1_[0,R](C) in the physical space, C=sum C_e, and Q=I-P. Since P commutes
with C, compressing (1) with beta_e=s gives

    D=QHQ >= s C_Q+E_* >= (s c_+(R)+E_*) I_Q.            (2)

The middle operator lower bound, not just its smallest eigenvalue, will be used
by the energy-resolved certificate. It is valid even though Q does not commute
with the local plaquette Hamiltonians.

The e_p inputs are certified, not floating ground estimates. For a character
cutoff N and t=e_p/kappa_p below the analytic omitted Casimir floor, the earlier
one-loop Schur matrix at normalized coupling lambda_p/kappa_p is strictly
positive. Its outward-rounded integer LDL pivots prove that positivity.
The complete one-loop Schur factorization then gives h_p>=e_p. The finite matrix
alone is not the all-tail proof; that factorization and its analytic floor are
included from the continuation.

For s=1 use E_*=0 and the bare electric floor instead; there are no positive
allocated cycle weights in that case. The acceptance program handles it as a
separate branch and does not divide by kappa=0.

## What this repairs and what it does not

This reconstructs the missing proof used by the earlier25two-plaquette targets.
Their exact matrices/targets need not change. The local full-space ground-state
argument is essential: a bound established only after imposing unrelated local
constraints would not automatically be valid when those cells are assembled.

This is a finite-graph comparison. The sum E_* may improve an extensive vacuum
floor, but it is not itself a uniform excitation gap, a continuum limit or a
renormalization prescription. The positivity-improving input and general
Schur theory are established tools, not claimed new discoveries here.
