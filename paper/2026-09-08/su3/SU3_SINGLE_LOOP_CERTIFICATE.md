# SU(3) single Wilson-loop spectral certificate

Executed 8 September 2026. Status: a computer-assisted certificate for the full, infinite-dimensional Hilbert space of a single compact SU(3) Wilson-loop degree of freedom. It is neither a finite-matrix-only claim nor a four-dimensional continuum Yang–Mills mass-gap proof. No Lean verification was run for this module.

## The concrete model and what is standard

Let Haar measure have total mass one and set

\[
\mathcal H=L^2(\mathrm{SU}(3),dU)^{\mathrm{Ad}},\qquad
H_{\kappa,\lambda}=\kappa C_2+\lambda(3-\operatorname{Re}\chi_{1,0}),
\quad \kappa>0,\ \lambda\geq0.
\]

Here the superscript Ad means conjugation-invariant functions, not the adjoint representation. Irreducible characters \(\chi_{p,q}\), \(p,q\geq0\), form an orthonormal basis. The potential is multiplication by a real nonnegative bounded function: \(|\operatorname{Tr}U|\leq3\). The electric operator is diagonal, with

\[
C_2(p,q)=\frac{p^2+q^2+pq+3p+3q}{3}.
\]

These ingredients are standard representation theory and Hamiltonian lattice gauge theory; their use here is not a claim to invent them. The canonical lattice Hamiltonian goes back to [Kogut and Susskind, Physical Review D 11 (1975), 395](https://journals.aps.org/prd/abstract/10.1103/PhysRevD.11.395). A directly inspected modern primary source gives the electric-Casimir and magnetic-plaquette Hamiltonian, the representation basis, gauge constraints, and representation truncations in [Ciavarella and Bauer, arXiv:2402.10265v2, equation (1) and surrounding discussion](https://arxiv.org/html/2402.10265v2). We use exact SU(3) characters; we do not import that paper's large-color approximation.

For an isolated square plaquette, fixing three edges along a spanning tree leaves its holonomy U and a residual conjugation symmetry. All four electric link Casimirs agree on a character. In the convention \(H=(g^2/2)\sum_l E_l^2-(1/g^2)\operatorname{Re}\operatorname{Tr}U\), adding the constant \(3/g^2\) gives \(\kappa=2g^2\), \(\lambda=1/g^2\). The experiments below simply specify \(\kappa=1\) and several ratios \(\lambda/\kappa\); they do not fix a physical energy scale. “Single loop” describes this degree of freedom, not a perturbative loop expansion.

Since \(C_2(p,q)\to\infty\) as \(p+q\to\infty\), the electric operator has compact resolvent. A bounded potential preserves self-adjointness on the electric domain and compact resolvent. Thus the full model has ordered eigenvalues \(E_0\leq E_1\leq\cdots\), counted with multiplicity.

## The exact character matrix

The quadratic Casimir formula follows from \(C_2(\Lambda)=\tfrac12\langle\Lambda,\Lambda+2\rho\rangle\), with \(\Lambda=p\omega_1+q\omega_2\), \(\rho=\omega_1+\omega_2\), and fundamental-weight Gram matrix

\[
\begin{pmatrix}2/3&1/3\\1/3&2/3\end{pmatrix}.
\]

The fundamental character rule is

\[
\chi_{1,0}\chi_{p,q}=\chi_{p+1,q}+\chi_{p-1,q+1}+\chi_{p,q-1},
\]

with terms having negative labels omitted. This can be checked as an identity, not only by sampling. For \(z_1z_2z_3=1\), the Weyl alternant numerator is the determinant with column exponents \((p+q+2,q+1,0)\). Multiplication by \(z_1+z_2+z_3\) is the sum of the three determinants obtained by increasing one exponent by one. The first two terms give the first two characters; for the last, factor \(z_1z_2z_3=1\) and reduce all exponents by one. A wall term vanishes through repeated columns. The antifundamental rule is obtained by exchanging p and q. Therefore multiplication by \(\operatorname{Re}\chi_{1,0}\) is half the sum of these two rules.

Let \(P_N\) retain \(p+q\leq N\), with \(r_N=(N+1)(N+2)/2\). Put \(Q_N=1-P_N\) and write

\[
H=\begin{pmatrix}A&B\\B^*&D\end{pmatrix}
\]

on \(P_N\mathcal H\oplus Q_N\mathcal H\). The finite matrix A has diagonal \(\kappa C_2(p,q)+3\lambda\) and entry \(-\lambda/2\) for each allowed fundamental or antifundamental neighbor. All entries are rational for rational couplings.

## The entire omitted sector and its boundary

For fixed \(s=p+q\),

\[
C_2(p,q)=\frac{s^2-pq+3s}{3}\geq
m(s):=\frac{s^2-\lfloor s^2/4\rfloor+3s}{3}.
\]

The maximum \(pq=\lfloor s^2/4\rfloor\) is attained at the balanced labels. The function m(s) increases with nonnegative integer s. Since the potential is nonnegative, the entire omitted sector satisfies

\[
D\geq d_N I,\qquad
 d_N=\kappa\,\frac{(N+1)^2-\lfloor (N+1)^2/4\rfloor+3(N+1)}{3}.
\]

Only retained characters on the outer shell \(p+q=N\) couple to omitted characters, and only to the first omitted shell \(p+q=N+1\). A retained state \((p,N-p)\) has exactly two outward neighbors:

\[
(p+1,N-p),\qquad(p,N-p+1).
\]

Thus the nonzero part of B is \(-\lambda/2\) times the transpose of the rectangular two-neighbor incidence matrix. On the retained outer shell,

\[
BB^*=\frac{\lambda^2}{4}
\begin{pmatrix}
2&1&0&\cdots\\
1&2&1&\cdots\\
0&1&2&\cdots\\
\vdots&\vdots&\vdots&\ddots
\end{pmatrix}.
\]

Every other row and column of \(BB^*\) is zero. Hence

\[
\|B\|=\lambda\cos\frac{\pi}{2N+4}\leq\lambda.
\]

The norm equality follows from the elementary tridiagonal eigenvalues \(2+2\cos(k\pi/(N+2))\). For the certificates we use the simpler exact rational bound \(b=\lambda\).

## Two valid ways to certify a gap

Write the first two eigenvalues of A as \(\mu_0\leq\mu_1\). A scalar block bound is

\[
E_1\geq L(\mu_1,d,b):=
\frac{\mu_1+d-\sqrt{(d-\mu_1)^2+4b^2}}2,
\qquad E_0\leq\mu_0.
\]

Indeed, remove the single retained ground-state vector and apply the two-by-two quadratic-form bound on its codimension-one orthogonal complement, followed by the min–max principle. This deliberately discards where the coupling acts.

A sharper certificate retains the actual boundary matrix. For rational \(z<d\), define

\[
M_N(z)=A-zI-\frac{BB^*}{d-z}.
\]

**Boundary certificate.** Suppose M_N(z) has exactly one negative eigenvalue and no zero eigenvalues. If a certified upper bound r for \(\mu_0\) satisfies \(r<z\), then

\[
\boxed{E_1-E_0\geq z-r>0.}
\]

**Proof.** Since \(D-z\geq(d-z)I>0\), the full Schur complement is

\[
S(z)=A-zI-B(D-z)^{-1}B^*\geq M_N(z).
\]

The min–max principle implies that S(z) has at most one negative eigenvalue. Completing the quadratic form in the omitted component shows that the negative index of \(H-z\) equals that of S(z); this is legitimate because B has finite rank and \((D-z)^{-1}\) is bounded. The trial subspace \(P_N\mathcal H\) provides \(E_0\leq\mu_0\leq r<z\), so \(H-z\) has at least one negative eigenvalue. Therefore exactly one full eigenvalue lies below z, and \(E_1\geq z\). Subtract the ground-state upper bound. □

This is a finite certificate about an infinite operator. It works because the estimate on D covers all omitted representations, not just a larger test cutoff.

## Executed results

All entries in the final column are proved lower bounds for the full single-loop model, in units of \(\kappa\). The scalar column is a conservative decimal presentation of an exact rational lower bound; a negative value means that particular estimate is inconclusive.

| \(\lambda/\kappa\) | N | retained dimension | scalar lower bound | boundary certificate for \((E_1-E_0)/\kappa\) |
|---:|---:|---:|---:|---:|
| 0 | 1 | 3 | 4/3 | 4/3 exactly |
| 0.1 | 3 | 10 | 1.2852796 | 1.2868372 |
| 1 | 6 | 28 | 1.2758093 | 1.3401688 |
| 10 | 10 | 66 | 2.0814038 | 5.6481431 |
| 100 | 25 | 351 | −33.3376127 | 19.3607700 |

The largest-coupling case is the clearest demonstration: the norm-only correction cannot certify a positive gap at N=25, while retaining the shell on which coupling occurs certifies a gap above 19.36077. This is evidence for preserving matrix and boundary support information in a verifier; it is not evidence for a continuum mass value.

Finite matrix eigenvalues were independently enclosed as follows. The decimal endpoints below are exact terminating rational numbers, not error bars estimated from convergence.

| \(\lambda/\kappa\) | finite \(\mu_0\) enclosure | finite \(\mu_1\) enclosure | certified full \(E_1\geq z\) |
|---:|---:|---:|---:|
| 0.1 | [0.2961080, 0.2961085] | [1.5829461, 1.5829466] | 1.5829457 |
| 1 | [2.5198544, 2.5198549] | [3.8600240, 3.8600245] | 3.8600237 |
| 10 | [11.2158942, 11.2158947] | [16.8641367, 16.8641372] | 16.8640378 |
| 100 | [38.5784689, 38.5784694] | [57.9392397, 57.9392402] | 57.9392394 |

The lower endpoints for finite \(\mu_0\) are not asserted as lower bounds for the full \(E_0\); the variational ordering goes in the other direction. Only the finite upper endpoint r is needed in the full gap certificate.

## Arithmetic verification and reproducibility

Run the complete verifier from this directory:

```text
python su3_character_certificate.py
```

The default verification requires only Python's standard library. Optional `--generate` uses NumPy and SciPy solely to propose rational endpoints; it still accepts no result without the exact checks. The bundled target file already contains all endpoints, so users do not need those optional packages to reproduce acceptance.

The verifier represents each interval as two arbitrary-precision integers divided by \(2^{192}\). Every rational matrix entry is rounded outward using integer division. Every elimination update encloses \(a-bc/d\) through exact integer arithmetic. A pivot must have a strict sign; if its interval meets zero, verification fails. Thus every exact LDL pivot has a certified sign and Sylvester inertia determines the exact eigenvalue count below each rational shift.

For each nonzero coupling, four finite-matrix inertia computations certify the two eigenvalue enclosures, and a fifth computes the inertia of the rational boundary-Schur matrix. Executed totals were:

- 20 exact inertia certificates and 2,275 strictly signed pivot intervals.
- 1,000 exact arithmetic-containment checks.
- 2,106 exact character-rule evaluations using independent Weyl determinants at three rational complexified torus points, through p+q=25. These finite evaluations are regression checks; the general character identity is proved above.
- 10,416 exact boundary-Gram entries checked for N=0 through 30, plus 62 boundary/tail checks and three comparisons with independent Fraction-based LDL elimination.
- Total reported arithmetic and structural assertions: 13,587. The recorded execution took approximately 1.57 seconds after target proposal on this environment; runtime is not part of the mathematical claim.

Files:

- `su3_character_certificate.py`: complete generator and exact verifier.
- `certificate_targets.json`: rational endpoints and proposal-only numerical values.
- `su3_results.json`: exact rational results, display values, and verification status.
- `interval_pivot_witnesses.json`: all outward pivot endpoints, with scale and shift metadata, so signs and regenerated witnesses can be audited.

The trusted computational base is Python integer/Fraction arithmetic, this small verifier, and the mathematical argument above. It is a reproducible computer-assisted proof, not a proof-assistant-checked theorem. The exploratory SciPy eigenvalues are retained with an explicit numerical label and are not used as certificate evidence.

## What this closes and what remains

A compact single-loop Schrödinger operator already belongs to a standard setting in which a unique positive ground state and a positive spectral gap are expected from elliptic spectral theory. We make no novelty claim for that existence statement. The deliverable here is an explicit, reproducible numerical lower bound with certified control of every omitted representation. This closes a concrete test of the retained-sector/omitted-sector boundary method on a genuinely non-Abelian, gauge-invariant quantum Hamiltonian with an infinite representation tail. The boundary certificate remains informative where a global coupling norm bound fails badly.

It does not control a many-plaquette lattice, spatial volume growth, lattice spacing, a continuum quantum field theory, or a continuum physical mass gap. Those targets require compatible certificates that survive the relevant volume and continuum limits. None of the numbers above are in GeV, and no old SUKS-2 or CRFZD parameter enters this model.
