# Yang–Mills restart: non-Abelian projector geometry and quantitative gap preservation

**Research checkpoint for Jeromie N. Beasley — 8 September 2026**  
**Status:** written finite-dimensional/classical proofs, exact symbolic examples, and synthetic numerical controls. This is not a proof of four-dimensional quantum Yang–Mills existence or its continuum mass gap. It is not a fresh Lean certificate. No physical mass or CRFZD frequency has been fitted.

## Abstract

We restart the older SUKS-2 Yang–Mills proposal using the explicit objects in the subsequent operator-first programme. A graph frame already used to retain unitary information in the light/peeling work gives a concrete non-Abelian connection: for a smooth SU(3)-valued map U, the rank-three projector onto its graph has an orthonormal frame Q, connection A = Q†dQ, and curvature F = −(U†dU)∧(U†dU)/4. We exhibit two graph families with identical scalar quantum geometric tensors at a point but different non-Abelian curvature norms. This closes a finite geometric calculation left outside the trace-sector treatment of the earlier QGT manuscript. It does not establish that this restricted frame family parameterizes all Yang–Mills configurations. For the gap problem, two exact mechanisms are developed: a normalized Schur-coupling bound and a principal-angle bound for positive operators with a common zero-energy subspace. Causal elimination identifies an explicit history kernel, while counterexamples show why unchanged projectors, stable spectral clusters, and a limited set of decaying correlators do not establish a physical mass gap. The remaining target is stated as a uniform vacuum-excluded estimate for a genuine gauge-invariant cutoff theory together with construction of a nontrivial continuum limit. A standalone script executes 2,723 symbolic and numerical assertions on the declared examples.

## 1. Sources, scope, and the two readings

The source-recovery pass inspected the live `dicipler-pixel/operator-first` repository, its main branch and the metadata of 17 pull requests, together with selected source files on the active branches. It read the available source catalogue, the hypersurface recovery note, the complete 37-page *Elemental Peeling v3*, the complete 17-page August *Intrinsic Quantum Geometric Tensor*, the complete 16-page *Spectral Stress* copy, the knot-field checkpoint, and the overlap-bridge argument. The *Matter at a Scale v5* HTML was identified and its definitions, scale-invariance and gap/census sections were inspected directly. The light, soficity, original interface and other branches were also compared through their explicitly integrated source sections and catalogued identities. The source ledger lists these different levels of inspection.

The second pass rederived the mathematical bridges used below and tested their failure modes. It was not a second reading of every file in every repository or of every historical conversation. Some live Zenodo requests failed; recovered manuscript copies and the earlier catalogue do not establish that every newest public Zenodo file was independently fetched today. Nothing here upgrades an old reported run into a new run.

The older chat's proposed 14.14-Hz-to-GeV calculation, knot/particle identifications, and positive-three-scalar-Hessian claim are not inputs. What remains useful from that ancestry is the proposed role of noncommuting transport, retained topological information, interfaces, and history-dependent reduction. The new work gives these ideas definitions on which a proof can operate.

## 2. Keep four projectors distinct

| Symbol | Role | What it does not mean |
|---|---|---|
| P_c = QQ† | Rank-three color/subbundle projector in a fixed ambient bundle | Not the quantum vacuum projector |
| P_s | A spectral-cluster projector of a declared operator | Not automatically a spatial boundary split |
| P_b | A retained/hidden or boundary/interior split | Not necessarily invariant under the dynamics |
| P_Ω | Orthogonal projection onto the quantum vacuum space | Not a rank-three color frame |

The same algebra can apply to several of these objects. Their physical roles cannot be identified by reusing the letter P. In particular, if P_s is a spectral projector of H, then [H,P_s] = 0: eliminating its complement produces no off-block history kernel. A nontrivial physical interface generally uses a different, non-invariant split.

### Conventions

All matrix norms without a subscript are operator norms; ||·||_F is the Frobenius/Hilbert–Schmidt norm. A dagger denotes the conjugate transpose. Connections are anti-Hermitian, so F = dA + A∧A. On a Euclidean parameter domain, Tr(F†F) is nonnegative. The finite Hamiltonian and memory calculations use ħ = 1; physical units are restored explicitly only in the final transfer-operator target. The four-dimensional base is specified, not derived from the projector.

The labels are preserved: TMF means Temporal Memory Field; CRFZD is the user's Cosmic Resonant Zeta Dynamics; OTKP means Over-Twisted Knot Potential. No cosmic interpretation is required to prove the statements here.

## 3. A concrete non-Abelian bridge from the graph lift

Let X be a smooth four-dimensional domain and U:X→SU(3) a C² map. Define

\[
Q_U=\frac1{\sqrt2}\begin{pmatrix}I_3\\U\end{pmatrix},\qquad
P_c=Q_UQ_U^\dagger
=\frac12\begin{pmatrix}I_3&U^\dagger\\U&I_3\end{pmatrix}.
\]

Then Q_U†Q_U = I₃ and P_c² = P_c = P_c†. These are precisely the frame and graph-projector identities, now applied to an SU(3) field rather than only an endpoint unitary.

### Proposition 1. Graph-frame connection and curvature

Set θ = U†dU. Then

\[
A=Q_U^\dagger dQ_U=\tfrac12\theta,\qquad
F=dA+A\wedge A=-\tfrac14\theta\wedge\theta.
\tag{1}
\]

In components,

\[
F_{\mu\nu}=-\tfrac14[\theta_\mu,\theta_\nu].
\tag{2}
\]

Both A and F are traceless and anti-Hermitian. For a change of frame Q→QG, G:X→SU(3),

\[
A\longmapsto G^\dagger AG+G^\dagger dG,
\qquad
F\longmapsto G^\dagger FG.
\tag{3}
\]

**Proof.** Differentiate U†U = I. This makes θ anti-Hermitian. Since det U = 1, Tr θ = d log det U = 0. Direct multiplication gives A = θ/2. The Maurer–Cartan identity dθ + θ∧θ = 0 gives (1). The trace of each commutator in (2) vanishes. Applying the product rule to QG gives (3). All statements are local bundle calculations, independent of a field equation. ∎

This distinction matters: θ itself is a flat pure-gauge connection. The induced connection θ/2 is generally not flat, because its derivative and quadratic terms have different coefficients.

### Proposition 2. The full projector retains matrix curvature

For an arbitrary orthonormal frame Q in a fixed trivial Hermitian ambient bundle, let P = QQ† and B_μ = (I−P)∂_μQ. Then

\[
F_{\mu\nu}
=\partial_\mu Q^\dagger(I-P)\partial_\nu Q
-\partial_\nu Q^\dagger(I-P)\partial_\mu Q
=B_\mu^\dagger B_\nu-B_\nu^\dagger B_\mu
=Q^\dagger[\partial_\mu P,\partial_\nu P]Q.
\tag{4}
\]

The intrinsic metric obeys

\[
g_{\mu\nu}=\tfrac12\operatorname{Tr}(\partial_\mu P\partial_\nu P)
=\operatorname{Re}\operatorname{Tr}(B_\mu^\dagger B_\nu).
\tag{5}
\]

**Proof.** Expand d(Q†dQ)+(Q†dQ)∧(Q†dQ), differentiate Q†Q = I, and insert I = P+(I−P). The P terms combine into A∧A with the required sign. For the last equality use ∂_μP = B_μQ†+QB_μ† and Q†B_μ = 0. The same block multiplication gives (5). ∎

In coordinate-free form the induced curvature is the endomorphism-valued two-form P dP∧dP P, acting on Ran P. A choice of frame displays its matrix entries. It is therefore too strong to say the traceless curvature is absent from the full Grassmannian projector field. It is absent from the scalar trace-sector QGT record. With a nontrivial ambient connection, replace d by its covariant derivative and include ambient curvature; a changing ambient frame must not be ignored.

One immediate upper bound is

\[
\|F_{\mu\nu}\|_F\le2\|B_\mu\|_F\|B_\nu\|_F
=2\sqrt{g_{\mu\mu}g_{\nu\nu}}.
\tag{6}
\]

This is not a lower bound on excitation energy. Reversing that implication would repeat the old gap error.

### An exact witness: same scalar QGT, different SU(3) curvature

At the origin of U(x,y) = exp(xX)exp(yY), take either

\[
X_c=i\operatorname{diag}(1,-1,0),\qquad
Y_c=\frac{i}{\sqrt3}\operatorname{diag}(1,1,-2),
\]

or

\[
X_n=E_{12}-E_{21},\qquad
Y_n=i(E_{12}+E_{21}).
\]

In both cases,

\[
g=\tfrac12 I_2,\qquad \operatorname{Tr}F_{12}=0.
\]

But

\[
\boxed{
\|F_{12}^{(c)}\|_F^2=0,\qquad
\|F_{12}^{(n)}\|_F^2=\tfrac12.
}
\tag{7}
\]

For the second pair [X_n,Y_n] = 2i diag(1,−1,0), which proves (7) directly. Thus the scalar QGT at a point does not determine even the quadratic non-Abelian curvature density at that point. This is an exact member of the programme's “same reduced record, different retained structure” examples. It is a local witness, not a statement that all derivatives of the scalar record agree on a neighbourhood.

The four generators E₁₂−E₂₁, i(E₁₂+E₂₁), E₂₃−E₃₂, i(E₂₃+E₃₂) generate an eight-dimensional real Lie algebra under commutators. The code checks this independently. This test concerns their Lie algebra, not a theorem identifying the full holonomy group of every chosen graph field.

### Scope: why this is not yet the Yang–Mills theory

The connection construction is standard in universal-connection and subbundle geometry; the useful contribution here is the explicit integration with the project's graph lift and the exact discrimination witness. Narasimhan–Ramanan-type universal-frame constructions use sufficiently large frames to represent general connections [R2]; the particular graph Q=(I,U)/√2 is a restricted family.

There is also a concrete perturbative warning. For U_ε = exp(εχ),

\[
\theta_\epsilon=\epsilon d\chi+O(\epsilon^2),\qquad
F_{\mu\nu,\epsilon}=-\frac{\epsilon^2}{4}[\partial_\mu\chi,\partial_\nu\chi]+O(\epsilon^3).
\]

Therefore the quadratic curvature action restricted to this graph family begins at order ε⁴ near U=I, not with a generic quadratic transverse gauge-field term. Simply substituting this U into an action would give a restricted theory. A claim of equivalence to pure Yang–Mills requires a sufficiently general parameterization, its constraints and measure, and the correct local dynamics. Those are not supplied by (1).

For a general orthonormal U(3) frame the connection need not be traceless; an SU(3) formulation also needs the determinant sector fixed. Our explicit graph example already has Tr A=0. A global frame on a trivial domain also does not represent every possible topological bundle sector without patching.

## 4. Turn positivity after elimination into a quantitative gap margin

The newer hypersurface/peeling work distinguishes a physical split from a spectral selection and gives an exact Schur complement. The following is the finite quantitative extension needed for a gap programme.

Work after removing a known vacuum subspace, and suppose the excitation operator has a Hermitian block decomposition

\[
H_{\rm ex}=\begin{pmatrix}A&B\\B^\dagger&D\end{pmatrix},\qquad A>0,\quad D>0.
\]

No identification of this matrix with a Yang–Mills cutoff Hamiltonian is assumed in the algebraic theorem.

### Proposition 3. Normalized coupling bound

Put

\[
C=A^{-1/2}BD^{-1/2},\qquad c=\|C\|<1.
\]

Then

\[
(1-c)\operatorname{diag}(A,D)\preceq H_{\rm ex}
\preceq(1+c)\operatorname{diag}(A,D),
\tag{8}
\]

and therefore

\[
\boxed{
\lambda_{\min}(H_{\rm ex})\ge
(1-c)\min\{\lambda_{\min}(A),\lambda_{\min}(D)\}.
}
\tag{9}
\]

**Proof.** For x,y write u=A^{1/2}x, v=D^{1/2}y. The cross term is 2 Re⟨u,Cv⟩ and its absolute value is at most c(||u||²+||v||²). Adding the diagonal terms proves (8) and (9). Equivalently the normalized block matrix has eigenvalues 1±s_j(C), and possibly additional ones. ∎

A uniform margin c≤c_*<1 and a uniform lower bound on the diagonal energies supply a uniform gap. Merely knowing c<1 separately at each cutoff does not.

### Proposition 4. Schur-margin bound

Let

\[
S=A-BD^{-1}B^\dagger\succeq sI,\quad D\succeq dI,\quad
\kappa=\|D^{-1}B^\dagger\|.
\]

For s,d>0,

\[
\boxed{
H_{\rm ex}\succeq\frac{\min(s,d)}{(1+\kappa)^2}I.
}
\tag{10}
\]

**Proof.** Factor

\[
H_{\rm ex}=L^\dagger\begin{pmatrix}S&0\\0&D\end{pmatrix}L,
\quad L=\begin{pmatrix}I&0\\D^{-1}B^\dagger&I\end{pmatrix}.
\]

The inverse triangular matrix has norm at most 1+κ. Hence ||Lz||≥||z||/(1+κ); the form inequality follows. ∎

At real z below the spectrum of D, the energy-dependent complement is

\[
S(z)=A-zI-B(D-zI)^{-1}B^\dagger,
\]

and

\[
S'(z)=-I-B(D-zI)^{-2}B^\dagger\preceq-I.
\tag{11}
\]

The compression of (H−zI)⁻¹ to the retained block equals S(z)⁻¹ whenever both sides exist. This can be used for rigorous low-energy exclusion, with the eliminated-block spectrum separately controlled. Block congruence preserves positivity/inertia but not numerical eigenvalues; that is why an estimate such as (10), rather than the determinant identity alone, is required.

### Sharp failure example

For 0<ε<1,

\[
H_\epsilon=\begin{pmatrix}1&1-\epsilon\\1-\epsilon&1\end{pmatrix}
\]

has diagonal block gaps both equal to one, but

\[
\lambda_{\min}(H_\epsilon)=\epsilon,\qquad
\|C\|=1-\epsilon,\qquad S=2\epsilon-\epsilon^2.
\]

The normalized bound (9) is exact. An argument that only checks positivity of the finite blocks would miss the collapse. Conversely, failure of a sufficient bound for some different family would not by itself prove that family's gap closes.

## 5. A second finite gap route: principal-angle gluing

### Proposition 5. Gap from transverse zero-energy subspaces

Let H₁,H₂ be positive Hermitian matrices, P₁,P₂ their orthogonal kernel projectors, and R the projector onto ker H₁∩ker H₂. Suppose

\[
H_1\succeq a(I-P_1),\qquad H_2\succeq b(I-P_2),\quad a,b>0,
\]

and set c=||P₁P₂−R||<1. Then

\[
\boxed{
H_1+H_2\succeq
\frac{a+b-\sqrt{(a-b)^2+4ab c^2}}2 (I-R).
}
\tag{12}
\]

For a=b this is a(1−c).

**Proof.** Remove the intersection and use the orthogonal principal-angle decomposition of two projections. On a two-dimensional block with angle θ, the matrix a(I−P₁)+b(I−P₂) has trace a+b and determinant ab sin²θ. Its smaller eigenvalue is

\[
\frac{a+b-\sqrt{(a-b)^2+4ab\cos^2\theta}}2.
\]

The largest surviving cosine is c. The remaining one-dimensional blocks have energies a,b, or a+b, so the displayed lower bound applies there as well. Positivity of H_j−a_j(I−P_j) finishes the proof. ∎

### Exact common-vacuum example

In C³ take P₁ onto span(e₀,e₁), P₂ onto span(e₀,cosθ e₁+sinθ e₂). The common vacuum is e₀. For H_j=I−P_j the two individual gaps are one but the summed gap is

\[
\Delta(\theta)=1-\cos\theta\sim\theta^2/2.
\]

At θ=0.1 it is 0.00499583472; at θ=0.001 it is about 4.99999958×10⁻⁷. Thus not just the local energies but also the relative subspace geometry must be controlled.

This is the precise useful role of the principal-angle programme. It does not say that more alignment always improves a gap. Nearly identical zero-energy spaces can leave a nearly unpenalized direction outside their intersection.

**Restriction.** Pure Yang–Mills is not automatically a frustration-free sum whose electric and magnetic pieces share zero-energy ground states. Applying (12) requires constructing appropriate positive comparison operators with the stated kernel properties. Calling two physical terms H₁ and H₂ does not establish those hypotheses. This route and the Schur route are distinct sufficient estimates, not independent proofs of the physical conclusion.

## 6. The old memory idea obtains an exact dynamical object

Take a fixed physical split and a time-independent Hermitian generator,

\[
i\dot x=Ax+By,\qquad i\dot y=B^\dagger x+Dy.
\]

Variation of constants gives

\[
y(t)=e^{-itD}y_0-i\int_0^t e^{-i(t-s)D}B^\dagger x(s)\,ds,
\]

and hence

\[
\boxed{
\dot x(t)=-iAx(t)-iBe^{-itD}y_0
-\int_0^t K(t-s)x(s)\,ds,
\quad K(t)=Be^{-itD}B^\dagger.
}
\tag{13}
\]

The same eliminated sector produces the resolvent self-energy

\[
\Sigma(z)=B(zI-D)^{-1}B^\dagger.
\tag{14}
\]

Equations (13) and (14) are time-domain and resolvent-domain descriptions of one eliminated subsystem. They are a defensible replacement for an unspecified TMF multiplier in this restricted setting.

If F_off = P_b H(I−P_b)+(I−P_b)HP_b, then

\[
\|F_{\rm off}\|_F^2=2\operatorname{Tr}(BB^\dagger)=2\operatorname{Tr}K(0).
\tag{15}
\]

Thus B=0 iff K(0)=0 iff K is identically zero. For a spectral split of the same Hermitian H, B=0. A spectral gap used to define P_s must not silently be reinterpreted as a nontrivial coupling B relative to P_s.

This elimination statement is not a proof of physical quantum non-Markovianity under every operational definition, nor of a cosmic memory field. Initial hidden data y₀ cannot be dropped without a preparation assumption. In a gauge theory, Gauss constraints also complicate a naive inside/outside tensor factorization; a legitimate split must respect the physical state space or an explicitly controlled boundary extension.

## 7. Which gap is being measured?

### Projector geometry does not determine the energy scale

For r>0, H↦rH+sI preserves eigenspaces and their projectors while scaling excitation gaps by r. More strongly, H_ε=diag(0,ε,1) has fixed individual projectors but variable gap ε. Consequently a subspace metric or integer rank cannot by itself determine an energy gap. This is the useful scale distinction from *Matter at a Scale*, not a reason to abandon projector methods.

The following objects must remain distinct: a band gap, a spectral-cluster separation, a Hessian curvature, an entanglement-spectrum gap, a dynamical relaxation rate, and the vacuum-excluded energy gap of the quantum gauge theory. Isospectral relaxation cannot generate a gap that was absent in the generator's spectrum.

### A complete measured correlation can miss the lowest excitation

For H_ε=diag(0,ε,1), Ω=e₀, choose O connecting e₀ only to e₂. Then

\[
\langle O\Omega,e^{-tH_\epsilon}O\Omega\rangle=e^{-t}
\]

for every ε, despite the true gap being ε. A second probe connecting to e₁ sees e^{-εt}. This is an exact instance of the newer light/peeling observability programme: a perfectly known reduced response can miss a low-energy state.

For a finite Hermitian H and observation matrix W, a useful sufficient completeness test is

\[
\operatorname{span}\{\operatorname{ran}W,H\operatorname{ran}W,\ldots,H^{n-1}\operatorname{ran}W\}
=\mathbb C^n.
\tag{16}
\]

Then the matrix response W†(z−H)⁻¹W sees every spectral sector. A scalar moment or a small selected family may not. Equation (16) is stronger than necessary to detect just the lowest eigenvalue, but is a checkable sufficient condition for full cyclicity.

### Conditional spectral-theorem transfer to the quantum target

Suppose a quantum theory has already been constructed with H≥0 and vacuum Ω. Suppose vectors OΩ with O centered and gauge-invariant span a dense subspace of Ω⊥, and for a common Δ>0 each such vector satisfies

\[
\langle O\Omega,e^{-tH}O\Omega\rangle\le C_O e^{-\Delta t}\quad(t\ge0).
\tag{17}
\]

Then H restricted to Ω⊥ has spectrum in [Δ,∞). To prove this, write each correlation as a positive spectral integral. Positive spectral weight in [0,E] with E<Δ would force a term at least w e^{-Et}, contradicting (17) at large t. The low-energy spectral projection therefore kills a dense set and is zero.

This is a conditional implication. Neither construction of the continuum theory nor the decay bound for a dense observable family is supplied by the finite matrix tests.

## 8. What the topology and spectral-boundary papers contribute

The recovered knot-field checkpoint distinguishes ordinary knot invariants, Hopf charge, representation color, spectral flow, and physical observables. It also explicitly leaves the knot-complement APS operator, adjoint torsion, and complete gluing constructions unimplemented. Preserve those boundaries.

A knot/holonomy representation can label loop observables and topological sectors. An index or winding number can constrain admissible deformations. A Riesz block can remain regular when its internal eigenvalues collide. These are useful tools for keeping information through a change of description. None alone supplies a lower bound on all positive quantum energies.

For instance, rescaling an invertible elliptic operator D to D/L preserves its index and eigenvectors while shrinking its nonzero eigenvalues by 1/L. Discrete topological labels and dimensionful gap scales are not interchangeable. A unitary SU(3) gauge representation must also not be conflated with the non-unitary SL(2,C) representations used in some hyperbolic torsion examples.

The *Spectral Stress* example is valuable precisely because it separates internal spectral collision from external cluster separation. For Yang–Mills, putting the vacuum together with arbitrarily low excited states inside one protected block would protect a description while failing to prove the required gap above the vacuum.

### Positivity guard for topological restrictions

A mathematical no-zero or admissibility guard is not automatically a permissible modification of a quantum lattice measure. Creutz's result [R4] shows that, for the stated class of single-plaquette weights with regularity assumptions, a hard admissibility cutoff eliminating an open region conflicts with a positive transfer matrix. This is not a prohibition on every possible topology-aware formulation. It is a specific warning that a proposed restriction must preserve the reconstruction/positivity assumptions rather than discard inconvenient configurations and thereby manufacture a gap.

## 9. The actual Yang–Mills target

The Clay formulation requires a nontrivial quantum Yang–Mills theory on four-dimensional spacetime, with specified mathematical field-theory properties and a positive mass gap [R1]. The stated problem is for every compact simple gauge group; an SU(3) construction would settle that case, not automatically the entire group family.

A mathematical regulator is not borrowed experimental data. For example, group-valued link variables, gauge transformations at vertices, Haar integration, plaquette observables and the Gauss-law physical subspace define a conventional cutoff problem. Using that definition keeps the target fixed. An alternative projector/holonomy formulation must be proved equivalent or shown directly to meet the target; it cannot simply replace the problem with a different gapped model.

For a cutoff family H_{a,L} with its vacuum energy removed, the target is

\[
\boxed{
\inf_{\psi\perp\Omega_{a,L}}
\frac{\langle\psi,H_{a,L}\psi\rangle}{\|\psi\|^2}
\ge\Delta_*>0
}
\tag{18}
\]

uniformly along an appropriate continuum/infinite-volume scaling family, together with a nontrivial limiting theory and preservation of the required locality, positivity and covariance properties. Formal implications for unbounded operators require domains and quadratic-form hypotheses; the finite proofs above do not silently cover those issues.

For a positive normalized transfer operator T_{a,L}=exp(−a_t H_{a,L}/ħ) with vacuum eigenvalue one, (18) is equivalent to

\[
-\frac{\hbar}{a_t}\log\|T_{a,L}(I-P_\Omega)\|\ge\Delta_*.
\tag{19}
\]

The transfer gap itself approaches zero as a_t→0 even when the physical energy gap remains fixed. Requiring a fixed bound ||T(I−PΩ)||≤q<1 independent of a_t would be the wrong continuum scaling condition.

The operator-first route should therefore try to prove, for a legitimate gauge-compatible decomposition, either uniform estimates

\[
\lambda_{\min}A,\lambda_{\min}D\ge a_*>0,
\qquad \|A^{-1/2}BD^{-1/2}\|\le c_*<1,
\]

or uniform Schur margins s,d and bounded κ, or a valid positive comparison system with uniformly controlled principal angles. These are sufficient conditions, potentially too strong for a particular decomposition. Finding a useful decomposition is part of the research, not a free choice that may assume the conclusion.

A naive repeated estimate with factor 0.8 at each of n levels yields 0.8ⁿ→0. This is why “every scale passed” is insufficient without controlling accumulated losses and restoring physical units.

## 10. What was executed

`verify_restart.py` produced `results.json` using NumPy 2.3.5, SciPy 1.17.0 and SymPy 1.14.0, seed 20260908.

| Group | Actual test | Result |
|---|---|---|
| Graph-frame geometry | Exact orthonormality, idempotency, four-generator traceless/skew conditions | Exact identities pass |
| Non-Abelian curvature | Second-jet connection calculation, projector commutator, off-block formula | Exact agreement on all six coordinate pairs |
| Color algebra | Real Lie closure of the four displayed generators | Dimension 8 |
| Scalar-observable witness | Same metric/trace, unequal matrix-curvature norm | 0 versus 1/2 exactly |
| Local gauge changes | 40 random SU(3) frames and declared first derivatives | Maximum relative residual 5.24×10⁻¹⁵ |
| Wilson-loop calibration | Exact rectangle transports for a two-parameter graph field | Nontrivial unitary determinant-one loops; curvature error decreases linearly with side length |
| Schur bounds | 200 positive Hermitian block examples | Both lower bounds and the two-sided form estimate pass |
| Schur identities | Triangular factorization and retained resolvent | Maximum relative residual 4.20×10⁻¹⁶ |
| Memory identity | Off-block Frobenius norm versus 2 Tr K(0) | Pass |
| Gap failure control | Fixed diagonal block gaps, coupling tending to one | Full gap equals ε |
| Angle gluing | Common-vacuum examples, equal and unequal local gaps | Exact formula reproduced numerically |
| Probe completeness | Same visible correlator, different hidden gap; Krylov-rank controls | Dark channel distinguished when the probe span is enlarged |
| Scaling control | Repeated local loss factor | Positive finite factors but vanishing accumulated bound |

**Total: 2,723 passed assertions.** Many are repeated numerical controls of the same identities. They are not 2,723 independent physical discoveries, not new measured data, and not a Yang–Mills certificate. The scripts neither simulate a full gauge lattice nor implement a continuum limit.

No fresh Lean compilation was executed. Existing repository evidence stays attached to its original commit and theorem scope. No new proof was uploaded to GitHub or Zenodo in this pass.

## 11. Restart decision

Keep the old ambition to connect topology, noncommuting transport and the persistence of distinctions. Replace the old frequency-to-mass argument with an explicit gauge construction and a uniform spectral estimate. The newer work contributes in complementary roles:

- Graph projectors and QGT supply the non-Abelian geometric representation and expose scalar information loss.
- Hypersurface elimination and UPG supply physical block splits, self-energy and exact history kernels.
- Principal-angle geometry supplies a conditional gap-gluing estimate.
- Matter/offset work separates the energy scale from scale-blind geometry.
- Light/peeling observability work blocks false gap certificates based on incomplete probes.
- Knot/APS and spectral-stress work record which sectors and blocks survive, with their own operator and gluing hypotheses kept explicit.

The first unresolved proof task is now concrete: construct a gauge-compatible decomposition of an actual SU(3) cutoff theory and obtain margins in (9), (10), or a valid alternative that do not disappear under the required scale limits. A proof of that estimate must be accompanied by construction/identification of the nontrivial continuum theory. No “1.37 GeV” target, CRFZD fit, or assumed vacuum gap is used to close it.

## References

[R1] A. Jaffe and E. Witten, *Quantum Yang–Mills Theory*, official Clay problem description. https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf

[R2] F. Massamba and G. Thompson, *The Universal Connection and Metrics on Moduli Spaces*, arXiv:math/0311198 (2003). Reviews and uses the Narasimhan–Ramanan universal-connection construction. https://arxiv.org/abs/math/0311198

[R3] M. A. Oancea, T. B. Mieling and G. Palumbo, *Quantum geometric tensors from sub-bundle geometry*, Quantum 10, 1965 (2026), arXiv:2503.17163. https://arxiv.org/abs/2503.17163

[R4] M. Creutz, *Positivity and topology in lattice gauge theory*, arXiv:hep-lat/0409017 (2004). https://arxiv.org/abs/hep-lat/0409017

User source editions and pinned repository paths are listed in `SOURCE_AND_PROOF_LEDGER.md`. The written finite matrix arguments do not claim literature-wide novelty for Schur complements, principal-angle decompositions, the universal connection, or the spectral theorem. The purpose is a source-controlled Yang–Mills restart with executable witnesses and explicit remaining obligations.
