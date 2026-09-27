# A local frame for every smooth SU(3) connection

**8 September 2026. Written derivation; independently reviewed in this continuation.**

This is an explicit local construction within established universal-connection mathematics. It is not a claim of literature-wide novelty, a quantum change-of-variables theorem, or a global trivialization of every bundle.

## Theorem

Let W be a coordinate patch in R^d and let

\[
A=\sum_{\mu=1}^d\sum_{a=1}^8 a_{\mu a}(x)T_a\,dx^\mu
\]

be an su(3)-valued C^2 connection whose real coefficients are bounded on W. The T_a form any fixed real basis of traceless anti-Hermitian 3-by-3 matrices. Put m=8d, M=sup|a_{mu a}|, delta=1/(4m), and choose a constant K>2mM, with K>0. Define

\[
w_0=\tfrac12,\qquad w_{\mu a,\pm}=\delta\pm\frac{a_{\mu a}}{2K},
\qquad U_{\mu a,\pm}=\exp(\pm Kx^\mu T_a).
\]

Stack the blocks sqrt(w_0)I and sqrt(w_{mu a,+})U_{mu a,+}, sqrt(w_{mu a,-})U_{mu a,-} into a rectangular matrix Q. Then

\[
Q^\dagger Q=I_3,\qquad Q^\dagger dQ=A.
\]

For d=4 this uses 65 blocks, hence Q is 195-by-3. The size is sufficient; no optimality is asserted. Every C^2 connection has bounded coefficients on a sufficiently small relatively compact coordinate patch.

**Proof.** All weights are strictly positive. The sum of the 64 nonconstant weights in four dimensions is 1/2; adding w_0 gives 1. Since all block unitaries are unitary, Q-dagger Q=I. For each block,

\[
(\sqrt w U)^\dagger d(\sqrt w U)=\tfrac12dw\,I+wU^\dagger dU.
\]

The scalar derivatives sum to zero. Each one-parameter exponential gives U_{mu a,+}^dagger dU_{mu a,+}=K T_a dx^mu and the opposite sign for its partner. Its paired contribution is K(w_+-w_-)T_a dx^mu=a_{mu a}T_a dx^mu. Summation proves the connection identity. The standard induced-curvature identity then gives

\[
F=dA+A\wedge A=Q^\dagger(dP\wedge dP)Q,\qquad P=QQ^\dagger.
\]

No field equation or gap hypothesis entered the construction. QED.

## What this repairs

The equal-weight six-by-three graph in the restart only realizes A=(U-dagger dU)/2. Its restricted action begins quartically near its constant frame. Here, for A_epsilon=epsilon A, choose the same K on a bounded epsilon interval and vary the weights. Then exactly

\[
F_\epsilon=\epsilon dA+\epsilon^2 A\wedge A.
\]

Thus the usual quadratic curvature action has its expected order-epsilon-squared term when dA is nonzero. At epsilon=0 this representation uses a spatially varying frame with a flat induced connection; it need not use a constant projector.

For a particularly transparent test let T=i diag(1,-1,0) and

\[
A=T(x^1dx^2+x^3dx^4).
\]

Then F=T(dx^1 wedge dx^2+dx^3 wedge dx^4) and

\[
\operatorname{Tr}(F\wedge F)=-4\,dx^1\wedge dx^2\wedge dx^3\wedge dx^4.
\]

The larger frame realizes this exactly on a bounded patch. The equal-weight graph cannot: its second-Chern density vanishes pointwise. This example is a local curvature witness; it is not a finite-action instanton on all of R^4.

## What is still required

Right multiplication Q->QG implements the usual gauge law for the connection. However, the coefficient-based prescription A->Q(A) is a choice of representative and need not satisfy Q(A^G)=Q(A)G. Different rectangular frames can represent the same A and can have different scalar projector metrics. Consequently, an action built from the full represented curvature agrees locally with the classical Yang-Mills action, but an arbitrary action built from the scalar projector metric need not. Integrating a flat measure over all Q is not automatically the Yang-Mills quantum measure.

Global patching, redundancy/constraints, the measure and Jacobian, and a suitable quantum construction remain separate obligations. This theorem closes the local representation question, not those obligations.

## Verification and attribution

`verify_frame.py` checks exact rational weight identities and exact integer-matrix curvature-density controls, then evaluates full 195-by-3 frames with analytic first derivatives at deterministic test points. Their curvature is compared with the prescribed connection's independently computed first-jet formula. Numerical tolerances are reported as numerical tolerances, not formal proof certificates.

The general universal-connection framework predates this programme. The explicit proof here can be read independently; see Massamba and Thompson, *The Universal Connection and Metrics on Moduli Spaces*, especially Sections 3.1 and 4, for Narasimhan-Ramanan constructions, representative non-equivariance and instanton frames: [primary paper](https://arxiv.org/abs/math/0311198).
