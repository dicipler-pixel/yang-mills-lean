# Local electric tails and a gap transfer without the absolute-vacuum window

Jeromie N. Beasley research programme — 9 September 2026

**Status:** a written operator argument developed in this workstream, with the
assumptions below. It is not a Lean formalization. The accompanying finite-model
checks test implementations and several failure modes; they are not the proof.
No historical priority over general truncation, Sylvester-equation, or
Rayleigh–Ritz theory is claimed. The current-source comparison is in the source
ledger. In particular, energy cancellation through a modified Hamiltonian has
an important recent precedent in Yang, Kane and Jabeen (2026), and rigorous
truncation theory in Tong et al. (2022).

## 1. Model and the obstruction being removed

Let E be a finite set of oriented links with configuration space SU(3)^E. A
plaquette is a simple closed link loop in which each participating link occurs
once, with orientation +1 or -1. Work either on the full L2 space with product
Haar measure or its subspace invariant under all vertex gauge transformations.
With standard Casimir normalization,

    H = sum_e alpha_e C_e + sum_p lambda_p [3 - Re Tr U_p],
    alpha_e > 0, lambda_p >= 0,
    C_2(p,q) = (p^2+q^2+pq+3p+3q)/3.

The kinetic operator is elliptic on a compact connected manifold. A bounded real
potential preserves compact resolvent and positivity improvement of the heat
semigroup. Thus the ground state is unique and strictly positive. Gauge
invariance of H and uniqueness imply that its ground state is gauge invariant;
the full-space and physical ground energies are identical. This observation is
used only to justify a variational comparison. The physical Hilbert space is
not assumed to tensor-factor over links.

The earlier global total-electric cutoff used an absolute hidden floor d. If the
ground energy grows with volume, d can fall below E0 even while the actual gap
stays positive. Subtracting the same scalar from H, r and d does not change
this obstruction. The following bound compares a *local* omitted sector to E0
without computing E0 and without assuming the gap one wants to prove.

## 2. A relative hidden-sector floor

For one link e put Lambda_e = sum_{p containing e} lambda_p. Let H_rest,e omit
alpha_e C_e and all plaquette potentials containing e. It acts on the remaining
link variables. Its ground energy is denoted E_rest,e. Trial with the constant
normalized function on link e and a ground state of H_rest,e. The Haar integral
of a single fundamental matrix or its conjugate is zero; therefore each removed
plaquette has trial expectation 3 lambda_p, regardless of the other links.
Consequently

    E0(H) <= E_rest,e + 3 Lambda_e.                         (2.1)

For the single-link cutoff P_e,N selecting p+q <= N, let Q_e,N = I-P_e,N. These
projectors commute with all gauge transformations, all link Casimirs and
H_rest,e. The minimum Casimir on a shell of size s is

    c(s) = [s^2 - floor(s^2/4) + 3s]/3.

It increases strictly for integral s >= 0: c(2k)=k^2+2k and
c(2k+1)=k^2+3k+4/3. Since the potential is nonnegative, on the entire omitted
single-link sector, including every state of every other link,

    D_e,N := Q_e,N H Q_e,N
           >= E_rest,e + alpha_e c(N+1)
           >= E0(H) + alpha_e c(N+1) - 3 Lambda_e.        (2.2)

This is a quadratic-form bound on the self-adjoint compression, not a diagonal
approximation to its magnetic term. Its offset from E0 is independent of the
number of distant links.

For U in SU(3), Re Tr U is between -3/2 and 3. To see the lower endpoint, write
its eigenvalues as exp(ia), exp(ib), exp[-i(a+b)] and use

    3 + 2[cos a+cos b+cos(a+b)] = |1+exp(ia)+exp(-ib)|^2 >= 0.

Thus 0 <= 3-Re Tr U <= 9/2. Centering each incident potential gives

    ||Q_e,N V_e P_e,N|| <= b_e := (9/4) Lambda_e.         (2.3)

The subtraction of a scalar does not affect an off-diagonal block.

## 3. The full low-energy subspace has a recursive tail bound

Fix omega > 0 and let R be the spectral projection of H onto the *closed*
window [E0,E0+omega]. The window may contain degeneracies. No separation of its
eigenvalues and no prior positive excitation gap is required. At a fixed finite
lattice R has finite rank and maps into the operator domain.

Multiplication by a fundamental character matrix element on link e tensors its
representation with 3; conjugate multiplication tensors with bar(3). The rules

    (p,q) x (1,0) = (p+1,q) + (p-1,q+1) + (p,q-1)

and the conjugate rule show that p+q changes by at most one. Invalid negative
labels are omitted. This applies to full Peter–Weyl matrix coefficients, not only
to class functions. Writing S_e,N=P_e,N-P_e,N-1, with P_e,-1=0, gives the exact
band relation

    Q_e,N H P_e,N = Q_e,N V_e S_e,N.                     (3.1)

Put u=E0+omega, T=H restricted to Ran R, and X=Q_e,N R, regarded as a map from
Ran R into Ran Q_e,N. The block eigenvalue equation is the Sylvester equation

    (D_e,N-u) X + X (u-T) = -Q_e,N V_e S_e,N R.          (3.2)

If delta_e,N := alpha_e c(N+1)-3 Lambda_e-omega > 0,
then D_e,N-u >= delta_e,N and u-T >= 0. The unique bounded solution is

    X = - integral_0^infinity exp[-t(D_e,N-u)]
                         Q_e,N V_e S_e,N R exp[-t(u-T)] dt.

The integral converges in norm. This is also obtained by differentiating the
product of the two semigroups; its terminal term tends to zero. Taking norms,
using (2.3), and S_e,N <= Q_e,N-1 proves

    ||Q_e,N R|| <= (b_e/delta_e,N) ||Q_e,N-1 R||.         (3.3)

Define exact scalar upper bounds by epsilon_e,-1=1 and

    epsilon_e,N = 1                                  if delta_e,N <= 0,
    epsilon_e,N = min(1, b_e epsilon_e,N-1/delta_e,N) otherwise.

Then ||Q_e,N R|| <= epsilon_e,N for every N. The recurrence is a sufficient
upper bound and may equal one even when the actual leakage is much smaller.

For large N, c(N+1) grows quadratically. At fixed couplings and omega the tail
therefore has a factorial-squared upper envelope (constant^N/(N!)^2 after a
finite initial segment). This conclusion follows from the nonperturbative
inequality (3.3), not from an unbounded-order perturbation-series extrapolation.
The constants and initial segment are coupling dependent.

## 4. Combining links without losing the local support

Choose one cutoff N_e >= 0 per link and define P=product_e P_e,N_e, Q=I-P. The
factors commute and preserve the physical Hilbert space. P has finite rank.
The elementary commuting-projector inequality Q <= sum_e Q_e,N_e gives

    ||Q R||^2 <= S := sum_e epsilon_e,N_e^2.             (4.1)

If S<1, P is injective on every subspace of Ran R.

For the Rayleigh–Ritz comparison we need more than a global potential norm. Fix
an ordering of E and telescope

    Q = sum_e F_e Q_e,N_e,    F_e=product_{f preceding e} P_f,N_f.

The summands are orthogonal projections. For a unit f in Ran R put x=Pf. A
plaquette term has no matrix element P V_p F_e Q_e,N_e when e is outside that
plaquette. When e is in the plaquette, its one-shell band rule puts the retained
end of this matrix element in S_e,N_e. Thus

    |<Pf,V_p F_e Q_e,N_e f>|
       <= (9 lambda_p/4) ||S_e,N_e Pf|| ||F_e Q_e,N_e f||
       <= (9 lambda_p/4) epsilon_e,N_e-1 epsilon_e,N_e.

Centering V_p is legitimate because the identity part has zero matrix element
between these orthogonal sectors. No commutation of F_e with V_p was used.
Summing only the actual incidences gives

    |<Pf,H Qf>| <= K := sum_e b_e epsilon_e,N_e-1 epsilon_e,N_e.    (4.2)

This is the useful retained-support refinement. It replaces a whole-lattice
norm times sqrt(S) with a sum of local boundary-tail products.

## 5. A quantitative gap transfer, with no full-gap premise

Let A=P H P on Ran P in the same (full or physical) Hilbert space. Suppose
S<1 and dim Ran P>=2. Let mu_0<=mu_1 be its first two eigenvalues. Define

    error = (omega S + K)/(1-S).                         (5.1)

For every j with E_j(H)-E0(H)<=omega,

    E_j(H) <= mu_j <= E_j(H)+error.                      (5.2)

Proof. The first inequality is variational. For the other direction use the
span R_j of the first j+1 eigenvectors and put u_j=E_j. For unit f in Ran R_j,
x=Pf and y=Qf, an exact expansion gives

    <x,(A-u_j)x>
      = <f,(H-u_j)f> - <Qf,Q(H-u_j)f> - <Pf,H Qf>.

Take real parts. The first term is nonpositive. The second has absolute value
at most omega S because (H-u_j) maps R_j to itself with norm at most omega and
||Q restricted to R_j||<=sqrt(S). The last term is bounded by (4.2).
Also ||x||^2>=1-S. The min-max principle on the (j+1)-dimensional image P R_j
proves (5.2). Complex inner products and possible eigenvalue degeneracies cause
no change to this argument.

In particular,

    gap(H) >= min{omega, mu_1-mu_0-error}.               (5.3)

If the actual gap exceeds omega, this is immediate. Otherwise apply (5.2) to
j=1 and E0<=mu0. A nonpositive right side is inconclusive, not a gaplessness
certificate. For a rigorous implementation replace mu1 by a certified lower
endpoint and mu0 by a certified upper endpoint. All budget quantities in
(5.1) are rational when the inputs are rational. Numerical eigensolvers are
not the acceptance mechanism for those endpoints.

## 6. Explicit volume dependence and what it does not prove

For a periodic three-dimensional cubic lattice of side L>=3 with equal alpha
and lambda, there are M=3L^3 links and M plaquettes. Each link is in four
plaquettes. Hence

    delta_N = alpha c(N+1)-12 lambda-omega,
    b_e = 9 lambda,
    S = M epsilon_N^2,
    K = 9 lambda M epsilon_N-1 epsilon_N.

The provided standard-library calculator chooses a cutoff giving a requested
error budget using exact fractions; it does not build that lattice Hamiltonian.
At fixed alpha,lambda,omega and target error, the factorial-squared bound yields
a sufficient N=O(log M/log log M) as M tends to infinity. Each single-link local
Hilbert dimension still grows as a polynomial of high degree in N, and the full
tensor dimension grows exponentially with M. Gauss constraints do not by
themselves remove that computational difficulty.

This changes the remaining proof obligation: an independently certified gap
of the *local-cutoff physical Hamiltonian*, with a controlled budget (5.1), can
be transferred to the untruncated finite lattice without requiring a global
absolute hidden floor above the extensive ground energy. It does not establish
that the finite-cutoff gap is uniform in volume or along a continuum trajectory.
The coupling-dependent initial cutoff diverges toward weak electric coupling;
physical rescaling, nontrivial continuum construction, and the field-theory
axioms remain separate unsolved tasks in this workstream.

## 7. Closely related prior methods

- Tong et al., Quantum 6, 816 (2022), arXiv:2110.06942v2: general rigorous local
  truncation and simulation bounds; its eigenstate theorem in Appendix H uses
  an isolated nondegenerate eigenvalue and a given separation delta. Our stated
  proof works on a complete low-energy window using the particular positive
  compact-group gauge Hamiltonian and does not assume that separation.
- Yang, Kane and Jabeen, Phys. Rev. D 114, 034517 (25 August 2026),
  doi:10.1103/9yly-8dy7; arXiv:2604.24896v2: modified-Hamiltonian ground-energy
  differences tighten bosonic tail bounds, assisted by Monte Carlo. The local
  ground-energy cancellation in Section 2 is conceptually related; the present
  constant-link Haar trial is analytic and does not import their simulations.
- Ciavarella et al., arXiv:2508.00061v4 (4 September 2026): truncation errors,
  including a leading-order factorial eigenstate analysis and tested gauge
  examples. Its perturbative scope is not silently upgraded to an all-orders
  SU(3) spatial gap theorem here.

No claim is made that these three papers exhaust the truncation literature.
