# What the hypersurface keeps: corrected theorem and a concrete gauge repair

**8 September 2026.** Audit of the supplied `what_the_hypersurface_keeps.md` against `RESTART(1).md`. This audit reads those supplied notes, not every original paper they mention. Their model-specific numerical values and literature-wide novelty are not re-certified here. The derivations below are finite or classical; no quantum mass gap is proved.

The proposed single “holonomy/discrete-wall theorem” is false as stated. There is a useful common practice—retain the object, its transformation law, its singular set and its measurements—but several different mathematical mechanisms are involved. Making those distinctions reveals a stronger limitation of the equal-weight graph and a small, explicit repair that recovers a classical instanton.

## 1. Corrections to the unification claim

| Draft claim | Precise replacement |
|---|---|
| A record, invariance and a wall set define holonomy. | Holonomy is parallel transport around a based closed loop for a specified connection. Its matrix changes by conjugation under a frame change. A conserved number or group-orbit invariant need not be holonomy. |
| Holonomy changes only on discrete walls. | General holonomy varies continuously with the connection and loop. Flatness gives homotopy invariance on a flat region. Gauge invariance gives invariance under changes of frame, a different operation. |
| The wall set is discrete. | Singular sets are often hypersurfaces or more complicated loci in a multi-parameter space. A one-parameter analytic family with nonidentically-zero determinant has isolated zeros; a smooth family need not. |
| Levine–Tristram signature jumps exactly at Alexander roots. | Away from the conventional exceptional point 1, discontinuities can occur only at Alexander roots; a root need not produce a nonzero jump. The winding of a separate complex map is another invariant with its own zero/pole locus. [Conway, Remark 2.1](https://arxiv.org/pdf/1903.04477) |
| Index, eta and winding are three integers. | Index and winding are integers under their usual hypotheses. Finite matrix signature is integer-valued. The analytically regularized APS eta invariant generally is real-valued and varies without a zero crossing. These three uses of “spectral asymmetry” require separate definitions. |
| Symmetry-breaking perturbations are walls and always move the trace at first order. | Particle–hole symmetry forces an exact zero. The symmetry-breaking directions form a tangent subspace; the trace can respond smoothly and its linear coefficient can vanish. They are not a discrete singular set. |
| An open-path angle integral or an Abel map is automatically holonomy. | An open-path phase needs endpoint frames or another comparison rule. Abel integrals require a curve, endpoints, differential and period lattice. Their ordinary values vary with endpoints; closed-cycle periods and flat-bundle monodromy are separate records. |
| A GL₂(Z) relabeling outside a line stabilizer is a wall. | The stabilizer supplies a sufficient score-preserving group action. A transformation outside it may still preserve counts/score or cease to define an admissible construction. The complement is not a differentiable wall set. |
| A particular ladder census limits every hypersurface to logarithmic capacity. | The quoted logarithmic law is a result for its stated one-dimensional free-fermion spectrum and resolution convention. It does not bound every hypersurface or higher-dimensional field theory. |

The exact determinant and symmetry statements in the offset work can survive these corrections. What must change is the inferred category and scope. Likewise the reported two parity labels, measured first derivatives and finite-size patterns remain source claims until their specific Hamiltonian, block, parameters and calculation are supplied.

An elementary eta counterexample makes the distinction explicit. On periodic functions on a circle, let `D_a = −i d/dx + a`, with spectrum `n+a`, `n∈Z`, and `0<a<1`. Then

\[
\eta_{D_a}(s)=\zeta(s,a)-\zeta(s,1-a),\qquad
\eta_{D_a}(0)=1-2a.
\]

Here the last identity follows from `ζ(0,a)=1/2−a`. The eta invariant moves continuously while no eigenvalue crosses zero. Its reduced value modulo integers is also generally nonconstant. This is an explicit calculation, not a statement about the unconstructed knot operator in the source corpus. Variation formulas for reduced eta and spectral flow are treated in [Dai–Li, *Asymptotic Spectral Flow*](https://arxiv.org/abs/2207.04811).

## 2. An exact Wilson-loop counterexample inside the restart's own graph

Embed `X=iσ₁`, `Y=iσ₂` into the upper `2×2` block of `su(3)` and put

\[
U(x,y)=e^{xX}e^{yY},\quad \theta=U^\dagger dU,\quad A=\theta/2.
\]

With parallel transport convention `dV/dt=−A(γ̇)V`, follow the rectangle `(0,0)→(a,0)→(a,b)→(0,b)→(0,0)`. Multiplying its four exact edge transports gives

\[
W(a,b)=e^{-bY/2}e^{aX/2}e^{bY/2}e^{-aX/2},
\qquad
\operatorname{Tr}_{3}W=3-4\sin^2(a/2)\sin^2(b/2).
\]

The trace varies smoothly when either side length varies in `(0,π)`. All rectangles are contractible and no singularity is crossed. At the origin,

\[
F_{xy}=-\tfrac14[X,Y]=\tfrac{i}{2}\sigma_3\ne0,
\qquad W=I-abF_{xy}+O(a^2b+ab^2).
\]

Thus the restart already supplies a direct counterexample to the draft's universal wall claim. It also supplies the corrected insight: matrix-valued transport retains curvature even while discrete topological labels remain unchanged.

## 3. The exact trace-selection theorem

Let `0<C<I` be a finite correlation matrix, and define

\[
K(C)=\log(I-C)-\log C,\qquad f(C)=\operatorname{Tr}K(C).
\]

If a unitary involution `J` obeys `JCJ=I−C`, functional calculus gives `JK(C)J=−K(C)`, hence `f(C)=0`. This proof uses strict eigenvalue bounds so that the finite trace logarithm is defined; it does not require a bulk Hamiltonian gap.

More generally, if `C(−δ)=I−JC(δ)J`, then `f(−δ)=−f(δ)`. Analyticity only implies

\[
f(\delta)=a_1\delta+a_3\delta^3+\cdots;
\]

it does not imply `a₁≠0`. For a differentiable perturbation `C′(0)=V`,

\[
f'(0)=-\operatorname{Tr}\bigl[(C_0^{-1}+(I-C_0)^{-1})V\bigr].
\]

Take `J` to swap entries 1↔2 and 3↔4, and take

\[
C(\delta)=\operatorname{diag}\left(
\tfrac14+\delta,\tfrac34+\delta,
\tfrac13-\tfrac{32}{27}\delta,\tfrac23-\tfrac{32}{27}\delta\right).
\]

For sufficiently small `|δ|`, `0<C(δ)<I`; its tangent is nonzero and breaks the fixed-point symmetry for `δ≠0`. Nevertheless `f′(0)=0` and `f‴(0)=−5120/81`, checked exactly in the accompanying script. No eigenvalue of `K` crosses zero near `δ=0`, either. This is an actual symmetry-breaking direction with a cubic response, not a reparameterization of a linear path.

## 4. A stronger restriction on the equal-weight graph

**Proposition.** For any smooth `U:X→SU(n)` and constant `c`, the connection `A=cU†dU` satisfies

\[
\operatorname{Tr}(F\wedge F)=0
\quad\text{pointwise}.
\]

**Proof.** Maurer–Cartan gives `F=c(c−1)θ∧θ`. Graded cyclicity gives

\[
\operatorname{Tr}(\theta\wedge\theta\wedge\theta\wedge\theta)
=(-1)^3\operatorname{Tr}(\theta\wedge\theta\wedge\theta\wedge\theta)=0.
\]

Multiplication by `c²(c−1)²` proves the claim. This is an exact local identity, not merely vanishing of an integrated characteristic number on a trivial bundle. ∎

Consequently `Q=(I,U)^T/√2` cannot be gauge-equivalent, even locally, to a connection with nonzero local second-Chern/Pontryagin density. Gauge transformations preserve that density. In Euclidean four dimensions it cannot contain any nonflat self-dual or anti-self-dual connection: when `F=±*F`, the vanishing of `Tr(F∧F)` forces the positive curvature norm `−Tr(F∧*F)` to vanish.

This strengthens the restart's existing warning that the ansatz is restricted. It does not invalidate the universal projector identity `F=Q†dP∧dP Q`, which holds for general orthonormal frames.

## 5. A compact constructive repair: variable weight and the instanton

Permit the graph weight to vary:

\[
Q_t=\begin{pmatrix}\sqrt{1-t}\,I\\\sqrt t\,U\end{pmatrix},
\qquad 0<t<1.
\]

The scalar normalization derivatives cancel, giving

\[
A=t\theta,\qquad F=dt\wedge\theta+t(t-1)\theta\wedge\theta,
\]

\[
\boxed{\operatorname{Tr}(F\wedge F)
=2t(t-1)\,dt\wedge\operatorname{Tr}(\theta\wedge\theta\wedge\theta).}
\]

The missing radial/weight derivative can therefore restore the local characteristic density. This formula does not make the weighted graph universal, but an especially small frame already recovers a standard instanton.

Let `ρ>0`, use coordinates `(x₁,x₂,x₃,x₄)` and their standard orientation, and put

\[
q=x_4I_2+i(x_1\sigma_1+x_2\sigma_2+x_3\sigma_3),\quad
r^2=\sum_{\mu=1}^4x_\mu^2,\quad D=\rho^2+r^2,
\]

\[
Q_\rho=\frac1{\sqrt D}\begin{pmatrix}\rho I_2\\q\end{pmatrix}.
\]

Because `q†q=r²I₂`, `Qρ†Qρ=I₂`. Away from `r=0`, it is exactly the variable-weight construction with `t=r²/D` and `U=q/r`; the combined frame is smooth at `r=0` even though `U` alone is undefined there. A direct calculation gives

\[
A_\rho=\frac{q^\dagger dq-\tfrac12d(r^2)I_2}{D},\qquad
F_\rho=\frac{\rho^2}{D^2}\,dq^\dagger\wedge dq.
\]

In the declared orientation this curvature is anti-self-dual:

\[
F_{12}=-F_{34},\quad F_{13}=F_{24},\quad F_{14}=-F_{23}.
\]

It satisfies the classical Yang–Mills equation `d_A*F=0`, since Bianchi gives `d_AF=0`. Its density and integral are

\[
\operatorname{Tr}(F_\rho\wedge F_\rho)
=\frac{48\rho^4}{(\rho^2+r^2)^4}\,d^4x,\qquad
\int_{\mathbb R^4}\operatorname{Tr}(F_\rho\wedge F_\rho)=8\pi^2.
\]

Under the convention `ν=−(8π²)⁻¹∫Tr(F∧F)`, this is `ν=−1`; reversing orientation reverses this sign. With action `S=−g⁻²∫Tr(F∧*F)`, it has `S=8π²/g²`. Adjoining a fixed orthogonal spectator column gives a `5×3` frame whose connection is `diag(Aρ,0)∈su(3)`.

This is the classical quaternionic BPST/ADHM instanton construction, rederived here as a repair to the project's graph representation, not a new instanton discovery. An explicit `4×2` universal frame for it appears in [Massamba–Thompson, §4.1, equation (4.1)](https://arxiv.org/pdf/math/0311198), with choices of orientation and quaternion convention accounting for sign differences.

The displayed frame is global on `R⁴`, not a global frame of its nontrivial compactification over `S⁴`; an additional chart and transition function are required at infinity. A constant-weight graph cannot evade the local zero-density obstruction by changing charts. This compact instanton subclass is also distinct from a general local universal-frame construction for arbitrary connections.

The parameter `ρ` remains an arbitrary classical size. Neither its topological charge nor its finite action establishes a quantum energy scale or mass gap. The contribution is precise: a hypersurface-oriented graph construction can retain genuine non-Abelian curvature, and allowing its weight to vary recovers nonzero characteristic density and an actual classical Yang–Mills solution.

## 6. Strongest valid combined statement

**The combined record must contain several kinds of information.** Discrete topological indices remain constant on suitable connected admissible families. Symmetry produces exact algebraic selection rules. Full parallel transport records connection geometry and usually varies continuously. A physical split can additionally retain an operator-valued self-energy and history kernel, as already proved in the restart. None of these records alone determines a quantum excitation gap.

For the Yang–Mills route, preserve the full curvature/transport data and the discrete sector data together, use sufficiently expressive frames, and then prove dynamics and uniform vacuum-excluded estimates for the actual gauge theory. Calling those distinct steps one holonomy theorem hides exactly the information the combined-eye programme is supposed to expose.

## Executed status

`verify_holonomy.py` is a complete executable script requiring SymPy. It passed **24 exact assertions** with SymPy 1.14.0: the Wilson trace, a generic component trace-four identity, the nonlinear symmetry response, quaternionic frame normalization, all six curvature components, anti-self-duality, the characteristic density and its exact radial integral. `holonomy_results.json` records the actual run and versions. The written arguments prove the general propositions; selected symbolic identities verify their concrete implementations. No Lean compilation or quantum gauge-theory simulation is claimed.
