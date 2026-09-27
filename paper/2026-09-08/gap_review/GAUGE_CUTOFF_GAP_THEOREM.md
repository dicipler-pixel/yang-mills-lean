# A gauge-compatible cutoff gap certificate without a known vacuum projector

Independent mathematical audit for the Yang–Mills continuation, 8 September 2026.

**Result.** A finite retained gauge-invariant sector, a lower energy bound on its entire complement, and a finite coupling estimate can certify the first gap of the untruncated finite-spatial-lattice Hamiltonian. The construction does not require knowing its exact ground state first. The missing Yang–Mills task remains control uniform in physical volume and lattice spacing, together with construction of the continuum theory.

## 1. Operator hypotheses and exact Schur inertia

Let

\[
\mathcal H=\mathbb C^m\oplus\mathcal K,\qquad m\ge2,
\qquad H=\begin{pmatrix}A&B\\B^\dagger&D\end{pmatrix},
\]

where \(A=A^\dagger\), \(D=D^\dagger\ge dI\), and \(B:\mathcal K\to\mathbb C^m\) is bounded. The domain of \(H\) is \(\mathbb C^m\oplus\operatorname{Dom}D\). This is a self-adjoint semibounded operator because it is a bounded self-adjoint perturbation of \(A\oplus D\). The Hilbert space can already be the Gauss-invariant physical space; no tensor-product decomposition across a spatial boundary is required.

For real \(z<d\), define

\[
S(z)=A-zI-B(D-zI)^{-1}B^\dagger,
\qquad R_z=(D-zI)^{-1}B^\dagger.
\]

The bounded invertible map

\[
L_z=\begin{pmatrix}I&0\\R_z&I\end{pmatrix}
\]

preserves the operator domain, since \(R_z\mathbb C^m\subset\operatorname{Dom}D\). Direct multiplication gives

\[
H-zI=L_z^\dagger\begin{pmatrix}S(z)&0\\0&D-zI\end{pmatrix}L_z.
\tag{1}
\]

Consequently

\[
\dim\mathbf1_{(-\infty,z)}(H)\mathcal H=n_-(S(z)),
\qquad \dim\ker(H-zI)=\dim\ker S(z).
\tag{2}
\]

Here \(n_-\) counts strictly negative eigenvalues with multiplicity. To justify (2) in the possibly infinite hidden sector, use the variational characterization of the negative index as the largest dimension of a strictly negative subspace of the closed quadratic form. The invertible congruence in (1) preserves that dimension. Its hidden diagonal block is strictly positive, so all negative directions are counted by the finite matrix \(S(z)\). Its nullspace is carried bijectively by \(L_z^{-1}\). If \(S(z)\) is invertible, (1) also gives a bounded inverse for \(H-zI\), so \(z\) lies in the resolvent, not merely outside the point spectrum.

The off-diagonal perturbation is finite rank. Thus the essential spectrum of \(H\) agrees with that of \(D\), if present, and has lower edge at least \(d\). Equation (2) also shows that at most \(m\) eigenvalues lie strictly below \(d\). Therefore spectrum below \(d\) consists of finitely many isolated eigenvalues of finite multiplicity. No independent assumption about a discrete low spectrum is needed under these hypotheses.

## 2. A closed-form gap lower bound

Write the eigenvalues of \(A\), with multiplicity, as

\[
\mu_0\le\mu_1\le\cdots\le\mu_{m-1}.
\]

Assume \(\mu_1<d\), and let \(\|B\|\le b\). The two-dimensional space spanned by the first two eigenvectors of \(A\), embedded as \((x,0)\), has largest Rayleigh quotient \(\mu_1\). The min–max principle therefore supplies two discrete eigenvalues \(\lambda_0\le\lambda_1<d\) of \(H\), and gives

\[
\lambda_0\le\mu_0,\qquad\lambda_1\le\mu_1.
\tag{3}
\]

For \(z<d\),

\[
S(z)\succeq A-zI-\frac{BB^\dagger}{d-z}
\succeq A-zI-\frac{b^2}{d-z}I.
\tag{4}
\]

Set

\[
L=\frac{\mu_1+d-\sqrt{(d-\mu_1)^2+4b^2}}2.
\tag{5}
\]

It is the smaller root of \((\mu_1-z)(d-z)-b^2=0\), and \(L\le\mu_1<d\). At \(z=L\), the second ordered eigenvalue of the final matrix in (4) is zero. That matrix has at most one strictly negative eigenvalue. The same holds for \(S(L)\), by eigenvalue monotonicity, and hence for \(H-LI\), by (2). Thus

\[
\boxed{\lambda_1(H)\ge L,\qquad
\lambda_1(H)-\lambda_0(H)\ge L-\mu_0.}
\tag{6}
\]

This is useful when \(L>\mu_0\). In that case the full ground state is simple, as a consequence of the certified separation. If \(L\le\mu_0\), this particular lower bound is inconclusive; it does not show that the true gap vanishes.

The correction to the finite compression is

\[
\mu_1-L=
\frac{2b^2}{\sqrt{(d-\mu_1)^2+4b^2}+(d-\mu_1)}
\le\frac{b^2}{d-\mu_1}.
\tag{7}
\]

The condition for a strictly positive certificate can equivalently be written

\[
\mu_1>\mu_0,\qquad
b^2<(\mu_1-\mu_0)(d-\mu_0).
\tag{8}
\]

This follows by testing the increasing quadratic threshold at \(z=\mu_0\). Formula (5) is sharp given only these spectral and norm data: take \(A=\operatorname{diag}(0,3)\), \(D=6\), and \(B=(0,2)^T\). The full eigenvalues are \(0,2,7\), and \(L=2\).

## 3. Stronger certificates retaining the boundary support

The first inequality in (4) retains where the coupling actually acts. It is often much sharper than replacing \(BB^\dagger\) by its largest eigenvalue times the identity.

Suppose an explicitly certified finite positive semidefinite matrix \(M\) satisfies \(BB^\dagger\preceq M\). For \(z<d\), put

\[
K_M(z)=A-zI-\frac{M}{d-z}.
\tag{9}
\]

**Exact certificate.** If

1. there is a nonzero vector \(v\) with \(v^\dagger(A-zI)v<0\); and
2. \(K_M(z)\) has at least \(m-1\) strictly positive eigenvalues,

then \(H\) has exactly one eigenvalue below \(z\), that eigenvalue is simple, and \(z\) belongs to the resolvent of \(H\).

**Proof.** Since \(S(z)\preceq A-zI\), condition 1 supplies a negative direction for \(S(z)\). Since \(S(z)\succeq K_M(z)\), condition 2 supplies at least \(m-1\) positive directions. A Hermitian \(m\)-by-\(m\) matrix with these two properties has exactly one negative eigenvalue, exactly \(m-1\) positive eigenvalues, and no zero eigenvalues. Apply (1)–(2). This proves the zero exclusion as well as the negative count. ∎

If \(r=v^\dagger Av/(v^\dagger v)<z\), then \(\lambda_0\le r\), and every other spectral value is strictly above \(z\). Whenever a second spectral value exists,

\[
\lambda_1-\lambda_0>z-r.
\tag{10}
\]

For reported closed lower bounds one may state \(\lambda_1-\lambda_0\ge z-r\). A separate better ground-state trial vector may replace \(v\) when calculating \(r\).

The original norm certificate is the special case \(M=\beta I\), with \(\beta\ge\|B\|^2\). Exact knowledge of \(\mu_0\) or \(\mu_1\) is unnecessary. For rational or algebraically certified inputs, prove condition 1 by exact arithmetic and condition 2 by giving an \(m\)-by-\((m-1)\) full-column-rank matrix \(W\) with

\[
W^\dagger K_M(z)W\succ0.
\tag{11}
\]

An exact positive \(LDL^\dagger\) factorization of (11), or positive leading principal minors, is a finite certificate. The correctness of the external bounds \(D\ge dI\) and \(BB^\dagger\preceq M\) remains part of the proof obligation. Floating-point guesses for these bounds are not enough.

For the sharp example above, take \(z=3/2\), \(d=6\), and the coarse \(M=4I\). Then

\[
K_M(z)=\operatorname{diag}(-43/18,11/18).
\]

The exact trial \(v=e_0\) has \(r=0\), and \(W=e_1\) certifies a positive gap greater than \(3/2\). The closed formula improves it to the exact value 2. Using \(M=BB^\dagger=\operatorname{diag}(0,4)\) avoids penalizing the uncoupled ground coordinate at all.

## 4. A genuine gauge-compatible finite spatial lattice

Fix a finite spatial lattice with oriented links \(E\), vertices \(V\), compact connected gauge group \(G=SU(3)\), and no matter fields. The kinematic Hilbert space is

\[
\mathcal H_{\mathrm{kin}}=L^2(G^E,dU),
\qquad
\mathcal H_{\mathrm{phys}}=\mathcal H_{\mathrm{kin}}^{G^V}.
\]

Each local gauge transformation acts by left and right translations on incident link variables. Let \(C_e\) be the nonnegative bi-invariant Casimir/Laplacian on link \(e\), and define \(C=\sum_e C_e\). Bi-invariance implies that every \(C_e\), and hence every spectral projection of \(C\), commutes with the entire local gauge group. This is the key compatibility fact; a generic matrix cutoff would not have it.

Choose the finite-rank electric cutoff

\[
P_R=\mathbf1_{[0,R]}(C)|_{\mathcal H_{\mathrm{phys}}},
\qquad Q_R=I-P_R.
\tag{12}
\]

The rank is finite because the Laplacian on the compact product \(G^E\) has compact resolvent. Equivalently, the Peter–Weyl decomposition has only finitely many representation labels below a Casimir bound, each with finite multiplicity. Restriction to the invariant subspace does not increase the rank. This is a spectral cutoff of the electric Casimir, not of the unknown full Hamiltonian, so its off-diagonal coupling need not vanish.

Write a fixed-convention pure-gauge Kogut–Susskind Hamiltonian as

\[
H=\alpha C+V_B,\qquad \alpha>0,
\qquad
V_B(U)=\sum_p\kappa_p\bigl(3-\operatorname{Re}\operatorname{Tr}U_p\bigr),
\quad\kappa_p\ge0.
\tag{13}
\]

The constants encode the chosen coupling, spacing and normalization. The magnetic multiplication operator is gauge invariant, nonnegative and bounded. The elementary trace bound gives

\[
0\le V_B\le M_BI,\qquad M_B=6\sum_p\kappa_p.
\tag{14}
\]

For SU(3) the sharper range \(\operatorname{Re}\operatorname{Tr}U\ge-3/2\) would replace 6 by \(9/2\), but the coarser bound (14) already suffices and uses only \(|\operatorname{Tr}U|\le3\). Equations (12)–(13) give the operator blocks

\[
A_R=P_RHP_R,
\quad B_R=P_RV_BQ_R,
\quad D_R=Q_RHQ_R.
\]

Let \(c_+(R)=\inf\sigma(C|_{\operatorname{ran}Q_R})\), assuming the complement is nonempty. Then \(c_+(R)>R\), and

\[
D_R\ge\alpha c_+(R)I=:d_RI,
\qquad
\|B_R\|\le M_B/2.
\tag{15}
\]

The improved coupling estimate follows from
\(B_R=P_R(V_B-M_BI/2)Q_R\) and \(\|V_B-M_BI/2\|\le M_B/2\). Direct evaluation of \(B_RB_R^\dagger\) or a local boundary-support estimate can be much better. The exact finite identity

\[
B_RB_R^\dagger=P_RV_B^2P_R-(P_RV_BP_R)^2
\tag{16}
\]

can sometimes calculate the coupling Gram matrix without constructing a vast complementary basis.

Thus Sections 1–3 apply to the **untruncated link Hilbert space on this fixed finite spatial lattice**, once their finite inequalities are established. Gauss invariance is built into both retained and hidden sectors. No assumption identifies the retained sector with the exact vacuum or with a spatial interior.

The Hamiltonian lattice framework is standard; Kogut and Susskind introduced its canonical formulation in 1975. Modern electric-basis truncation work studies how finite link Hilbert spaces approach that framework. The present calculations use elementary Schur/min–max machinery to supply the explicit certificate stated above; they are not a claim to invent the Kogut–Susskind theory or the Schur complement. [Kogut–Susskind, *Physical Review D* 11, 395](https://journals.aps.org/prd/abstract/10.1103/PhysRevD.11.395); [Ciavarella et al., *Truncation uncertainties for accurate quantum simulations of lattice gauge theories*](https://arxiv.org/html/2508.00061v2).

## 5. What is complete at fixed lattice, and what is not

At fixed spatial lattice, coupling and spacing, \(H=\alpha C+V_B\) has compact resolvent. The cutoff spaces exhaust its form domain: for a vector in the form domain of \(C\), spectral truncation converges in the \(\|u\|^2+\langle u,Cu\rangle\) norm, and the bounded potential does not change that form domain. The min–max principle then gives

\[
\mu_k(R)\downarrow\lambda_k(H)
\quad\text{as }R\to\infty
\tag{17}
\]

along increasing exhaustive cutoffs, for each fixed \(k\). Meanwhile \(d_R\to\infty\), and the bound \(b_R\le M_B/2\) is independent of \(R\). Equations (5) and (7) imply

\[
L_R-\mu_0(R)\longrightarrow\lambda_1(H)-\lambda_0(H).
\tag{18}
\]

Therefore, if the full fixed-lattice ground state is simple, this certificate is eventually positive as the electric cutoff is enlarged. For the connected compact configuration manifold and real bounded magnetic potential in (13), positivity improvement of the heat semigroup gives the familiar unique positive ground state; gauge symmetry makes that state invariant. This qualitative finite-volume result is already standard compact elliptic theory. The quantitative certificate adds an explicit bound with an accounted-for cutoff tail.

Neither (17) nor (18) is uniform in the number of links, plaquettes, physical volume or inverse spacing. In particular, \(M_B\) grows with the number of plaquettes and changes with the coupling and physical energy normalization. Finite-volume compactness disappears in the infinite-volume problem. A continuum mass-gap proof cannot be obtained by declaring the fixed-lattice limits uniform.

## 6. Multiscale loss accounting: exactly what is sufficient

Suppose proved comparison estimates in one consistent physical energy normalization give

\[
\Delta_{j+1}\ge(1-\eta_j)\Delta_j,
\qquad 0\le\eta_j<1,
\qquad\Delta_0>0.
\tag{19}
\]

Iteration gives

\[
\Delta_n\ge\Delta_0\prod_{j=0}^{n-1}(1-\eta_j).
\tag{20}
\]

The infinite product is strictly positive **if and only if** \(\sum_j\eta_j<\infty\). Indeed, \(-\log(1-x)\ge x\), while for \(0\le x\le1/2\), \(-\log(1-x)\le2x\). A summable sequence is eventually at most \(1/2\), and its finitely many earlier factors are positive. If additionally \(\eta_j\le\rho<1\), an explicit lower bound is

\[
\prod_j(1-\eta_j)\ge
\exp\!\left[-\frac{\sum_j\eta_j}{1-\rho}\right].
\tag{21}
\]

This is a necessary and sufficient condition for positivity of **this product certificate**. It is only a sufficient condition for an actual uniform gap. For example, \(\Delta_j=1\) and \(\eta_j=1/2\) satisfy (19) at every step, while the product lower bound tends to zero and the actual gaps remain one. Failure of a loose bound does not prove gap closure.

If a scale step also changes energy normalization by \(a_j>0\), the correct iteration is

\[
\Delta_n^{\mathrm{phys}}\ge\Delta_0^{\mathrm{phys}}
\prod_{j<n}a_j(1-\eta_j).
\tag{22}
\]

A positive uniform lower certificate is equivalent to
\(\inf_n\sum_{j<n}[\log a_j+\log(1-\eta_j)]>-\infty\).
Summability of losses alone does not settle this more general expression. The rescaling cannot be omitted when comparing dimensionless lattice gaps with a physical continuum mass.

Finally, passage of a uniform estimate to a limiting operator requires a construction of that operator. One sufficient abstract setup is strong resolvent convergence \(H_j\to H\), \(H_j\ge0\), strong convergence of their vacuum projections \(P_j\to P\), and a uniform inequality \(H_j\ge\Delta_*(I-P_j)\) with \(\Delta_*>0\). Strong convergence of the heat semigroups then yields

\[
\|e^{-tH}(I-P)\|\le e^{-t\Delta_*},\qquad e^{-tH}P=P,
\]

and the spectral theorem gives \(H\ge\Delta_*(I-P)\). Identifying such a limit with a nontrivial four-dimensional local quantum Yang–Mills theory requires additional work; the Schur certificates do not construct it.

## 7. Audit of the proposed general local frame

The separate frame construction proposed in the continuation also checks algebraically. Write an arbitrary bounded local anti-Hermitian traceless connection as

\[
A=\sum_{\mu=1}^4\sum_{a=1}^8 a_{\mu a}(x)T_a\,dx^\mu,
\]

with real coefficients and fixed anti-Hermitian traceless generators. Put \(m=32\), \(\delta=1/(4m)\), choose \(K>2m\sup_{x,\mu,a}|a_{\mu a}(x)|\), and set

\[
w_0=\tfrac12,
\quad w_{\mu a}^{\pm}=\delta\pm\frac{a_{\mu a}}{2K},
\quad U_{\mu a}^{\pm}=e^{\pm Kx^\mu T_a}.
\]

Stack the 65 three-by-three blocks \(\sqrt{w_0}I\) and \(\sqrt{w_{\mu a}^{\pm}}U_{\mu a}^{\pm}\) into a \(195\)-by-\(3\) frame \(Q\). All weights are strictly positive and sum to one, so \(Q^\dagger Q=I\). Moreover,

\[
Q^\dagger dQ
=\tfrac12\sum_i dw_i I+\sum_iw_iU_i^\dagger dU_i
=\sum_{\mu,a}K(w_{\mu a}^{+}-w_{\mu a}^{-})T_a\,dx^\mu=A.
\]

The derivative-of-weight terms cancel exactly. Noncommuting generators cause no extra cross terms because each block is differentiated before summing. For sufficiently smooth coefficients this removes the representational restriction of the earlier \((I,U)/\sqrt2\) graph family on a bounded coordinate patch. Global bundle topology, patch transitions, a field measure, and quantum dynamics remain separate questions.
