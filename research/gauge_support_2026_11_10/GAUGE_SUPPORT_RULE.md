# The SU(3) gauge support rule (layer 2 of the 28/3 tail floor)

*Red, 2026-11-10. Status: the representation-theoretic core is proved in Lean
(`GaugeSupport.lean`, standard axioms only). The lattice wrapper (the basis and tensor
identifications below) is proved on paper here and is not yet formalized.*

## Setting

- Finite lattice graph Γ = (V, E) with each link e oriented, e = (s(e) → t(e)).
- Gauge group G = SU(3), compact. All representations are finite-dimensional, continuous,
  over ℂ. Irreps are written Irr(G); 1 is the trivial irrep.
- Link Hilbert space L²(G). By Peter–Weyl,
  L²(G) = ⊕_{π ∈ Irr(G)} V_π ⊗ V_π* (Hilbert direct sum),
  where a gauge transformation (h_v)_v acts on the link variable U_e by
  U_e ↦ h_{s(e)} U_e h_{t(e)}⁻¹. On the block V_π ⊗ V_π* the factor V_π is acted on by
  h_{s(e)} and V_π* by h_{t(e)} (one fixed convention; the other convention swaps π and π*
  throughout and changes nothing below).
- Spin-network decomposition: H = ⊗_e L²(G) = ⊕_{π : E → Irr(G)} ⊗_e (V_{π_e} ⊗ V_{π_e}*).
  Regrouping factors by vertex,
  ⊗_e (V_{π_e} ⊗ V_{π_e}*) ≅ ⊗_v W_v(π),
  W_v(π) := (⊗_{e : s(e)=v} V_{π_e}) ⊗ (⊗_{e : t(e)=v} V_{π_e}*),
  and the gauge group ∏_v G acts factor by factor, the v-th copy of G on W_v(π).
- A state ψ ∈ H is gauge invariant iff it is fixed by ∏_v G. Since the decomposition over
  π is G-stable, ψ is gauge invariant iff each component ψ_π is, and
  (⊗_v W_v(π))^{∏_v G} = ⊗_v W_v(π)^G
  (invariants of an outer tensor product of finite-dim reps of a product group are the
  tensor product of the invariants; use complete reducibility of each W_v).
- **Support** of ψ: supp(ψ) = { π : ψ_π ≠ 0 }; for one labelling π, the *non-trivial links*
  are N(π) = { e : π_e ≠ 1 }. "Support graph" = the subgraph formed by N(π).

## Statement (gauge support rule)

Let ψ be gauge invariant and π ∈ supp(ψ). Then at every vertex v:

(a) **No dangling link.** v is not incident to exactly one link of N(π).

(b) **Two-valent vertices pass the same irrep through.** If v is incident to exactly two
links e, f of N(π), then, writing ε_v(e) = π_e if v = s(e) and π_e* if v = t(e)
(the irrep that link contributes to W_v), we have ε_v(f) ≅ ε_v(e)*.
Equivalently: if one of e, f leaves v and the other enters it, π_e ≅ π_f; if both leave
(or both enter), π_f ≅ π_e*.

## Proof

Since ψ_π ≠ 0 lies in ⊗_v W_v(π)^G, every factor W_v(π)^G is nonzero. Fix v.
Trivial-irrep links contribute factors 1 = ℂ, so W_v(π) ≅ ⊗_{e ∈ N(π), e ∋ v} ε_v(e).
(A loop link at v contributes V ⊗ V* to W_v itself; the graphs in question are
bipartite, so they have none.)

(a) If exactly one non-trivial link e meets v, W_v ≅ X := ε_v(e), a simple
non-trivial representation. A nonzero invariant x ∈ X^G spans a G-stable line, so by
simplicity X = ℂx and G acts trivially on X, contradicting X ≇ 1. Hence W_v^G = 0, a
contradiction. (Lean: `GaugeSupport.no_invariant_single`.)

(b) If exactly two, W_v ≅ X ⊗ Y with X = ε_v(e), Y = ε_v(f) simple. For finite-dim X the
canonical map X ⊗ Y → Hom(X*, Y) is a G-equivariant linear isomorphism, so
(X ⊗ Y)^G ≅ Hom_G(X*, Y). X* is simple since X is (a G-stable subspace of X* has a
G-stable annihilator in X). By Schur's lemma (kernel and image of an intertwiner are
G-stable) a nonzero intertwiner X* → Y between simples is an isomorphism, and
conversely an isomorphism is a nonzero intertwiner. So W_v^G ≠ 0 iff Y ≅ X*.
(Lean: `GaugeSupport.schur`, `GaugeSupport.pair_invariant_iff_iso`,
`GaugeSupport.pair_invariant_zero_of_not_iso`, applied with ρ = X*, σ = Y.)
For SU(3) one may also note dim Hom_G(X*, Y) ≤ 1 over ℂ (algebraically closed Schur);
this is not needed for the support rule.

## What is assumed and what is not

Used: G a group whose link-variable representations are finite-dimensional and completely
reducible (true for compact G: unitary trick / Haar averaging); Peter–Weyl for L²(G) for
the spin-network basis; finite-dimensionality for X ⊗ Y ≅ Hom(X*, Y). The two Lean
theorems themselves need only an arbitrary group and an arbitrary field: no algebraic
closure, compactness, finite dimension or characteristic assumption.

Not used: anything specific to SU(3) (dimension 8, rank 2, the Casimir values), any
symmetry of the graph, or the Hamiltonian. The rule restricts which labellings can
carry weight; it says nothing about energies, and the Casimir bounds (layer 1) are separate.

Not claimed: the rule does not exclude vertices of degree ≥ 3 in N(π)
(e.g. 3 ⊗ 3 ⊗ 3 has an invariant for SU(3)), nor supports where the same link
carries several irreps across different components ψ_π (each π is treated separately).

## How it feeds `SmallSupportsAreCycles` (layer 3, PR #11)

By (a), for every π ∈ supp(ψ) with N(π) ≠ ∅, the support graph N(π) has minimum degree
≥ 2 (no vertex of degree 1; degree-0 vertices are simply absent). This is exactly the
"leaf-free" hypothesis of `SmallSupportsAreCycles`: on each of the five graphs, a
leaf-free edge set with ≤ 6 links is a single 4- or 6-cycle. Then (b) applied along the
cycle forces the same irrep (up to orientation conjugation) on every link of the cycle,
which is what the Casimir count in layer 1 uses: one irrep π ≠ 1 on all 4 or 6 links.

To close the 28/3 floor in Lean one still has to formalize: the per-vertex regrouping
and the invariants-of-a-tensor-product step above (pure linear algebra plus complete
reducibility), and the identification of the repo's support predicate with N(π).
