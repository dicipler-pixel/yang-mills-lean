---
title: "Retained Geometry and Certified Gauge Cutoffs"
subtitle: "An operator-first continuation toward Yang-Mills"
author: "Research programme of Jeromie N. Beasley"
date: "8 September 2026"
fontsize: 11pt
geometry: margin=0.85in
colorlinks: true
linkcolor: blue
urlcolor: blue
---

## Abstract

The restart supplied an induced non-Abelian connection and finite Schur gap bounds, but left their application to a genuine gauge operator unresolved. This continuation makes three concrete advances. First, the equal-weight graph is shown to have identically vanishing second-Chern density. A variable-weight graph recovers a classical instanton, and an explicit larger frame represents every smooth local SU(3) connection. Second, a gauge-compatible electric cutoff and an energy-dependent Schur certificate bound the first excitation without presupposing the exact vacuum. Third, exact arithmetic certificates establish positive gaps for an SU(3) one-plaquette Hamiltonian on its entire infinite-dimensional character space, with the omitted representation tail bounded analytically. Retaining the matrix support of the coupling succeeds in a case where a scalar norm bound fails. These results close a local representation problem and a fixed-lattice certification problem. The uniform spatial-volume/continuum estimate and construction of four-dimensional quantum Yang-Mills remain open.

## 1. What is being continued

The supplied restart distinguishes the color-frame projector, a spectral-cluster projector, a physical retained/hidden split, and the vacuum projector. That distinction is preserved. It also proves that scalar geometric records can lose matrix curvature, and that a selected correlation function can miss the lowest excitation. These are useful reasons to retain more information; they are not lower energy estimates by themselves.

The task identified by the handoff was to find a gauge-compatible decomposition of an actual SU(3) cutoff theory and control the energy lost through its coupling. An additional obstacle is that the restart's excitation-block estimates begin after removal of a known vacuum. The exact vacuum is generally unavailable in an interacting gauge problem. Section 4 replaces that requirement with a finite eigenvalue count and an explicit bound on the complete hidden sector.

All four supplied markdown files were read in this continuation. Their citations to older manuscripts and their report of 2,723 earlier checks remain inherited evidence. The earlier script was not supplied and that count was not rerun. Fresh checks and their scopes are listed in Section 8. No new Lean compilation is claimed.

## 2. What the equal-weight graph cannot retain

Let $U:X\to SU(n)$, $\theta=U^\dagger dU$, and $A=c\theta$ for constant $c$. Maurer-Cartan gives

$$F=c(c-1)\theta\wedge\theta.$$

**Proposition 1.** Every such connection satisfies $\operatorname{Tr}(F\wedge F)=0$ pointwise.

**Proof.** The matrix trace on differential forms is graded cyclic. Moving the first degree-one factor past the other three gives

$$\operatorname{Tr}(\theta^4)=(-1)^3\operatorname{Tr}(\theta^4)=0.$$

Multiplication by $c^2(c-1)^2$ proves the assertion. Here powers denote wedge products with matrix multiplication. This is a local identity, not merely a vanishing integrated characteristic number. $\square$

The restart's frame $Q=(I,U)^T/\sqrt2$ has $c=1/2$. It therefore cannot be gauge-equivalent even locally to a connection with nonzero second-Chern density. In Euclidean four dimensions, it also cannot represent a nonflat self-dual or anti-self-dual connection: if $F=\pm *F$, vanishing of $\operatorname{Tr}(F\wedge F)$ forces the nonnegative norm density $-\operatorname{Tr}(F\wedge *F)$ to vanish.

The full-projector formula remains valid:

$$F=Q^\dagger(dP\wedge dP)Q,\qquad P=QQ^\dagger.$$

The restriction belongs to the chosen family of frames, not to general projector geometry.

### 2.1 A compact repair with an actual classical solution

Allow the graph weight to vary:

$$Q_t=\begin{pmatrix}\sqrt{1-t}\,I\\\sqrt t\,U\end{pmatrix},\qquad
A=t\theta,\qquad F=dt\wedge\theta+t(t-1)\theta^2.$$

The scalar derivatives cancel in $Q_t^\dagger dQ_t$. Expansion gives

$$\operatorname{Tr}(F\wedge F)=2t(t-1)dt\wedge\operatorname{Tr}(\theta^3),$$

which can be nonzero. In particular, with Pauli matrices $\sigma_j$, set

$$q=x_4I_2+i\sum_{j=1}^3x_j\sigma_j,\quad r^2=\sum_{\mu=1}^4x_\mu^2,
\quad Q_\rho=\frac{1}{\sqrt{\rho^2+r^2}}\begin{pmatrix}\rho I_2\\q\end{pmatrix},\quad\rho>0.$$

Since $q^\dagger q=r^2I_2$, this frame is orthonormal and smooth on all of $\mathbb R^4$. Away from the origin it has $t=r^2/(\rho^2+r^2)$ and $U=q/r$; the combined frame is smooth where this separate $U$ is undefined. Direct differentiation yields

$$A_\rho=\frac{q^\dagger dq-\tfrac12d(r^2)I_2}{\rho^2+r^2},\qquad
F_\rho=\frac{\rho^2}{(\rho^2+r^2)^2}dq^\dagger\wedge dq.$$

In the orientation $(x_1,x_2,x_3,x_4)$, the six components obey

$$F_{12}=-F_{34},\qquad F_{13}=F_{24},\qquad F_{14}=-F_{23}.$$

Thus $F=-*F$, and Bianchi implies the classical Yang-Mills equation $d_A*F=0$. Exact symbolic calculation verifies

$$\operatorname{Tr}(F_\rho\wedge F_\rho)
=\frac{48\rho^4}{(\rho^2+r^2)^4}\,d^4x,\qquad
\int_{\mathbb R^4}\operatorname{Tr}(F_\rho\wedge F_\rho)=8\pi^2.$$

For $\nu=-(8\pi^2)^{-1}\int\operatorname{Tr}(F\wedge F)$ the charge is $-1$. An orthogonal spectator column gives a $5\times3$ frame and connection $\operatorname{diag}(A_\rho,0)\in\mathfrak{su}(3)$. This is the established quaternionic BPST/ADHM instanton, reconstructed here to repair the graph ansatz. The frame over $\mathbb R^4$ still needs a second chart for its nontrivial compactification over $S^4$. The classical size $\rho$ is free; no quantum mass scale follows. See the explicit instanton frame in [Massamba and Thompson, Section 4.1](https://arxiv.org/abs/math/0311198).

## 3. A frame for every smooth local SU(3) connection

The variable-weight example is still a subclass. The following explicit construction removes the local representational restriction altogether.

**Theorem 2.** Let $T_a$, $1\le a\le8$, be a real basis of traceless anti-Hermitian $3\times3$ matrices. On a coordinate patch $W\subset\mathbb R^4$, suppose

$$A=\sum_{\mu=1}^4\sum_{a=1}^8 a_{\mu a}(x)T_a\,dx^\mu$$

has real, bounded $C^2$ coefficients. Put $m=32$, $\delta=1/(4m)$ and choose a positive constant $K>2m\sup|a_{\mu a}|$. Define

$$w_0=\tfrac12,\qquad w_{\mu a,\pm}=\delta\pm\frac{a_{\mu a}}{2K},
\qquad U_{\mu a,\pm}=\exp(\pm Kx^\mu T_a).$$

Stack $\sqrt{w_0}I_3$ and the 64 blocks $\sqrt{w_{\mu a,\pm}}U_{\mu a,\pm}$ into a $195\times3$ matrix $Q$. Then

$$\boxed{Q^\dagger Q=I_3,\qquad Q^\dagger dQ=A.}$$

**Proof.** The weights are positive and sum to one. For one block,

$$(\sqrt w U)^\dagger d(\sqrt w U)=\tfrac12dw\,I+wU^\dagger dU.$$

The scalar terms sum to zero. The paired unitary terms contribute

$$K(w_{\mu a,+}-w_{\mu a,-})T_a\,dx^\mu=a_{\mu a}T_a\,dx^\mu.$$

Sum over all pairs. $\square$

Every smooth local connection has bounded coefficients after restricting to a sufficiently small relatively compact patch. The dimension is sufficient, with no optimality claim. This is an explicit instance of established universal-connection mathematics, not a discovery of universal connections.

The construction also removes the restart's quartic perturbative restriction: for $A_\epsilon=\epsilon A$ and one fixed admissible $K$,

$$F_\epsilon=\epsilon dA+\epsilon^2A\wedge A.$$

The curvature-squared action has the usual quadratic term when $dA\ne0$. At $\epsilon=0$, the chosen frame is spatially varying but induces a flat connection.

Right multiplication $Q\mapsto QG$ implements the correct gauge law. The coefficient prescription $A\mapsto Q(A)$ itself need not be gauge-equivariant. Global patching, the redundancy among frames, and the quantum measure/Jacobian remain open. In particular, integrating an arbitrary measure over $Q$ or replacing curvature energy with the scalar projector metric does not establish quantum equivalence. This distinction is also present in the [universal-connection literature](https://arxiv.org/abs/math/0311198).

## 4. Certifying the gap without assuming the vacuum

Let $\mathcal H=\mathbb C^m\oplus\mathcal K$, $m\ge2$, and

$$H=\begin{pmatrix}A&B\\B^\dagger&D\end{pmatrix},\quad A=A^\dagger,
\quad D=D^\dagger\ge dI,\quad B\text{ bounded}.$$

Use domain $\mathbb C^m\oplus\operatorname{Dom}D$. For real $z<d$, define

$$S(z)=A-zI-B(D-zI)^{-1}B^\dagger.$$

The bounded invertible triangular map

$$L_z=\begin{pmatrix}I&0\\(D-zI)^{-1}B^\dagger&I\end{pmatrix}$$

preserves the operator domain and gives

$$H-zI=L_z^\dagger\operatorname{diag}(S(z),D-zI)L_z.$$

By the negative-index characterization of a quadratic form, the number of full eigenvalues below $z$ is exactly the number of negative eigenvalues of $S(z)$. The kernels also correspond. If $S(z)$ is invertible, the factorization gives a bounded inverse for $H-zI$. This controls the complete hidden Hilbert space, not a second finite truncation of it.

### 4.1 A scalar estimate

Write $\mu_0\le\mu_1$ for the first two compression eigenvalues. If $\mu_1<d$ and $\|B\|\le b$, the min-max principle and the Schur bound give

$$E_0(H)\le\mu_0,\qquad
E_1(H)\ge\frac{\mu_1+d-\sqrt{(d-\mu_1)^2+4b^2}}{2}.$$

Indeed,

$$S(z)\succeq A-zI-\frac{b^2}{d-z}I.$$

At the displayed lower bound for $E_1$, the second eigenvalue of the right side is zero. It has at most one negative eigenvalue; so does the full operator shifted by that value. Subtracting $\mu_0$ supplies a gap certificate when positive. A nonpositive certificate is inconclusive.

### 4.2 Keeping the matrix support is stronger

Suppose $BB^\dagger\preceq M$ with a certified finite matrix $M\succeq0$. Define

$$\boxed{K_M(z)=A-zI-\frac{M}{d-z}.}$$

**Theorem 3.** Suppose $z<d$, $A-zI$ has a negative direction, and $K_M(z)$ has at least $m-1$ strictly positive eigenvalues. Then $H$ has exactly one eigenvalue below $z$, that eigenvalue is simple, and $z$ is in the resolvent of $H$. If a variational estimate gives $E_0(H)\le r<z$, then

$$\boxed{\Delta(H)\ge z-r.}$$

**Proof.** The inequalities

$$K_M(z)\preceq S(z)\preceq A-zI$$

give at least $m-1$ positive directions and one negative direction for the finite Hermitian matrix $S(z)$. These exhaust its dimension, excluding any zero eigenvalue. Schur inertia and the variational upper bound prove the claim. $\square$

This is the needed version of the retained-record principle for a gap proof. Replacing $BB^\dagger$ by $b^2I$ penalizes every retained direction equally, including directions the hidden sector does not directly couple to. Retaining the coupling's matrix support can avoid that loss. It does not require identifying the exact vacuum first.

## 5. A gauge-compatible cutoff of the actual lattice operator

Fix a finite spatial lattice with links $E$, vertices $V$ and plaquettes $p$. The physical pure-gauge Hilbert space is

$$\mathcal H_{\rm phys}=L^2(SU(3)^E,dU)^{SU(3)^V}.$$

Let $C=\sum_{e\in E}C_e$ be the sum of bi-invariant link Casimirs, and use a fixed normalization of the Kogut-Susskind Hamiltonian

$$H=\alpha C+V_B,\qquad
V_B=\sum_p\kappa_p(3-\operatorname{Re}\operatorname{Tr}U_p),\quad\alpha>0,\quad\kappa_p\ge0.$$

These are standard gauge-theory objects, with coefficients carrying the chosen energy normalization. The electric Casimir commutes with every local gauge transformation. Hence

$$P_R=\mathbf1_{[0,R]}(C)|_{\mathcal H_{\rm phys}}$$

is a gauge-compatible finite-rank cutoff. It is a spectral projector of the electric term, not of the full interacting Hamiltonian; the magnetic term couples across it. With $Q_R=I-P_R$,

$$A_R=P_RHP_R,\quad B_R=P_RV_BQ_R,\quad D_R=Q_RHQ_R.$$

If $c_+(R)$ is the smallest omitted Casimir, positivity of $V_B$ gives

$$D_R\ge\alpha c_+(R)I.$$

The potential is bounded. For example, the elementary trace inequality gives $0\le V_B\le M_BI$ with $M_B=6\sum_p\kappa_p$, and centering the potential gives $\|B_R\|\le M_B/2$. Its exact coupling Gram matrix is

$$B_RB_R^\dagger=P_RV_B^2P_R-(P_RV_BP_R)^2.$$

Therefore Theorem 3 applies inside the physical gauge-invariant space. No spatial tensor factorization or known interacting vacuum was assumed. The Hamiltonian framework is credited to [Kogut and Susskind](https://journals.aps.org/prd/abstract/10.1103/PhysRevD.11.395).

At a fixed spatial lattice, the compact configuration manifold gives compact resolvent. Electric cutoffs exhaust the form domain, so $\mu_j(R)\downarrow E_j(H)$. Meanwhile $d_R=\alpha c_+(R)\to\infty$ and $\|B_R\|$ remains bounded at that fixed lattice. The scalar certificate consequently converges to the actual gap. Positivity improvement of the compact-manifold heat semigroup with bounded real potential gives a simple positive ground state, which is gauge invariant by uniqueness. Thus a sufficiently large electric cutoff eventually certifies the positive fixed-lattice gap. This is a completeness statement for fixed-lattice certification, not a uniform continuum theorem.

## 6. Executed SU(3) certificates with the infinite tail controlled

To test the method on a genuine gauge operator that is explicit enough to verify exactly, consider the isolated one-plaquette reduction. After fixing a spanning tree, gauge-invariant functions are class functions of the remaining plaquette holonomy. Its Hilbert space is

$$\mathcal H=L^2(SU(3))^{\operatorname{Ad}},\qquad
H=\kappa C_2+\lambda(3-\operatorname{Re}\chi_{1,0}),\quad\kappa>0,\quad\lambda\ge0.$$

The single coefficient $\kappa$ absorbs the four equal edge electric contributions and the chosen normalization. This is a finite spatial gauge system with an infinite representation space. It is not a four-dimensional continuum field theory.

The characters $\chi_{p,q}$, $p,q\ge0$, are an orthonormal basis, and

$$C_2(p,q)=\frac{p^2+q^2+pq+3p+3q}{3}.$$

Multiplication by the fundamental character obeys

$$\chi_{1,0}\chi_{p,q}=\chi_{p+1,q}+\chi_{p-1,q+1}+\chi_{p,q-1},$$

with negative labels omitted; the conjugate rule supplies the other three neighbors. Consequently, the retained matrix for $p+q\le N$ has diagonal $\kappa C_2(p,q)+3\lambda$ and off-diagonal $-\lambda/2$ on those six-neighbor connections. Its dimension is $(N+1)(N+2)/2$.

For the entire omitted sector,

$$d_N=\frac{\kappa}{3}\left((N+1)^2-\left\lfloor\frac{(N+1)^2}{4}\right\rfloor+3(N+1)\right)$$

is a rigorous lower bound. At fixed shell number $s=p+q$, the minimum is $c(s)=(s^2-\lfloor s^2/4\rfloor+3s)/3$. Explicitly $c(2k)=k^2+2k$ and $c(2k+1)=k^2+3k+4/3$, so successive differences are $k+4/3$ and $k+5/3$, both positive. Thus the first omitted shell minimizes the Casimir over the entire complement. The nonnegative potential preserves this lower bound. No omitted representation is silently discarded. The Casimir tends to infinity with finite multiplicities, and the bounded potential preserves compact resolvent.

Only the shell $p+q=N$ couples to the complement. On this shell, $BB^\dagger$ has diagonal $\lambda^2/2$ and adjacent off-diagonal $\lambda^2/4$; all other entries vanish. In particular $\|B\|\le\lambda$. The certificate uses the full shell matrix in $K_M(z)$.

### 6.1 Results

All entries below are in units of $\kappa$, with $\kappa=1$. Positive lower bounds apply to the full untruncated one-plaquette operator.

| $\lambda/\kappa$ | $N$ | Retained dimension | Certified $\Delta/\kappa$ lower bound |
|---:|---:|---:|---:|
| 0 | 1 | 3 | $4/3$ exactly |
| 0.1 | 3 | 10 | 1.2868372 |
| 1 | 6 | 28 | 1.3401688 |
| 10 | 10 | 66 | 5.6481431 |
| 100 | 25 | 351 | 19.3607700 |

At $\lambda/\kappa=100$, the scalar norm certificate at the same cutoff is approximately $-33.33761265$, hence inconclusive. The boundary-matrix certificate is the exact positive rational

$$\boxed{\Delta/\kappa\ge\frac{1936077}{100000}=19.36077.}$$

This is a controlled example of the practical gain from retaining matrix information. A failed scalar lower bound did not mean that the actual gap had closed.

### 6.2 Why these are certificates rather than numerical guesses

Floating-point eigensolvers were used only to propose rational target intervals and a test energy $z$. Acceptance uses standard-library Python integers and fractions. Each exact rational matrix entry is enclosed on a $2^{-192}$ grid; every Schur elimination operation rounds outward. Every pivot interval must lie strictly on one side of zero. Sylvester inertia then fixes the exact number of negative eigenvalues.

For each nonzero coupling, four inertia calculations enclose the first two compression eigenvalues, and a fifth proves that $K_M(z)$ has one negative and all remaining positive eigenvalues. The certified upper endpoint $r$ for the compression ground state obeys $E_0(H)<r<z$. Theorem 3 then controls the full infinite tail. The complete pivot intervals and rational targets are included.

The run completed 20 exact inertia certificates, comprising 2,275 certified pivot signs. There are also 13,587 arithmetic/character/boundary assertions, including independent Weyl-character checks and small exact-fraction comparisons. Repeated checks are not counted as independent theorems. The verifier needs no NumPy, SciPy or network access to recheck the supplied certificate targets.

## 7. The corrected role of hypersurfaces, holonomy and memory

The accompanying audit finds that the draft's proposed universal discrete-wall holonomy theorem is too strong. General holonomy varies smoothly with a connection or loop. For the restart's own graph, a contractible rectangle has

$$\operatorname{Tr}_3W(a,b)=3-4\sin^2(a/2)\sin^2(b/2),$$

which varies without crossing a singular wall. A separate finite correlation example has a nonzero symmetry-breaking tangent but zero linear trace-log response and nonzero cubic response. Thus symmetry breaking does not automatically imply first-order motion. APS eta is also generally real and continuously variable; it must be distinguished from integer finite-matrix signature.

The useful combined record has several components with different jobs:

| Retained object | What it controls | Extra condition needed for Yang-Mills |
|---|---|---|
| Full frame/projector curvature | Local non-Abelian field geometry | Sufficient representation, patching and quantum measure |
| Holonomy and discrete sector labels | Transport and admissible topology | Defined connection, loop and sector hypotheses |
| Boundary coupling and self-energy | Influence of eliminated states | A lower bound on the complete hidden spectrum |
| Principal angles | Relative position of kernel subspaces | Valid positive comparison operators and energy penalties |
| Observable/probe family | Which excitations can be detected | Completeness for any correlation-based gap inference |
| Physical energy normalization | Comparison of gaps across scales | Correct cutoff factors and limiting dynamics |

For the spectral split used here, the retained sector is selected by the electric Casimir while the full generator includes the magnetic term. It can therefore have a nonzero off-block coupling. Its history kernel $Be^{-itD}B^\dagger$ and resolvent self-energy are two descriptions of the same eliminated sector. Their existence is not yet a uniform gap estimate; the Schur certificate supplies the energy test that was missing.

## 8. Proof and execution ledger

| Result | Evidence in this continuation |
|---|---|
| Constant-weight graph has zero second-Chern density | General graded-trace proof and exact component control |
| Variable-weight instanton repair | Written derivation; all six curvature components, duality and charge integral checked exactly |
| General local $195\times3$ frame | Written proof and independent review; 67 rational controls, 411 numerical comparisons |
| Gap certificate before vacuum subtraction | Operator-domain/Schur-inertia proof and independent review |
| Gauge-compatible electric cutoff | Casimir/Gauss commutation and complete-tail estimate proved |
| One-plaquette full-Hilbert gaps | Exact rational targets and 20 outward-interval inertia certificates |
| Discrete-wall and compulsory-linear-response claims | Explicit exact counterexamples in the audit |
| Uniform spatial-volume/continuum mass gap | Not proved |

The largest absolute Frobenius residual in the full local-frame comparisons was $8.40\times10^{-15}$. This is a floating-point implementation residual, not a quantum uncertainty. The 24 holonomy/instanton checks are exact SymPy calculations. The SU(3) certificate acceptance uses exact integer interval arithmetic. None of these is a Lean kernel certificate.

## 9. The unresolved estimate is narrower now

The gauge-compatible decomposition is now explicit. Fixed-lattice certification can account for the entire representation tail. What has not been controlled is the dependence on the number of links and plaquettes, physical volume, lattice spacing and coupling along a continuum trajectory. For example, the coarse bound on the magnetic potential grows with the plaquette count. The one-plaquette table gives no bound on that growth.

A precise next uniform target, stated without assuming the vacuum, is to produce physical-unit values $r_{a,L}<z_{a,L}<d_{a,L}$ for a family of genuine spatial lattices such that

$$E_0(H_{a,L})\le r_{a,L},\qquad z_{a,L}-r_{a,L}\ge\Delta_*>0,$$

and prove that

$$K_{a,L}(z_{a,L})=A_{a,L}-z_{a,L}I-
\frac{M_{a,L}}{d_{a,L}-z_{a,L}}$$

has at least $\dim A_{a,L}-1$ positive eigenvalues, with a certified negative trial for $A_{a,L}-z_{a,L}I$. More detailed resolvent bounds may improve this sufficient criterion when its scalar tail denominator is too coarse.

If instead a multiscale comparison uses $\Delta_{j+1}\ge(1-\eta_j)\Delta_j$ in one fixed physical normalization, its product lower bound stays positive exactly when $\sum_j\eta_j<\infty$, provided $0\le\eta_j<1$. This criterion concerns that bound, not necessity for a true gap. Changes of energy normalization introduce additional factors and must also be controlled. Repeated exact elimination at a fixed test energy can avoid some losses from multiplying independent coarse estimates, but its final Schur margin still needs a proof.

A positive estimate must accompany a nontrivial limiting quantum theory with the required field-theory properties. The [official Jaffe-Witten formulation](https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf) remains the target. SU(3) is the case treated here; the Clay problem asks for every compact simple gauge group.

The continuation therefore establishes a usable local representation and a gauge-compatible certification mechanism, with actual complete-tail certificates on a gauge Hamiltonian. It does not establish the four-dimensional quantum mass gap. The next missing proof is a spatial and physical-scale uniform estimate, rather than another finite positivity example.

## Reproducibility and source provenance

The package contains this paper in Markdown and PDF; the complete mathematical notes in `frame/`, `gap_review/` and `holonomy/`; the standard-library spectral verifier in `su3/`; exact targets and pivot witnesses; and immutable copies of the four supplied handoff files with hashes. The old manuscripts and repository commits cited by those handoffs were not silently upgraded to new readings or new verification runs.

Run `python su3/su3_character_certificate.py` to recheck the exact spectral certificates. Run `python frame/verify_frame.py` with NumPy/SciPy, and `python holonomy/verify_holonomy.py` with SymPy, for the separate geometric implementation checks. `README.md` gives complete commands and dependencies. No repository, Zenodo record or external publication was modified.
