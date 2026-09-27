# Complete C<=8 gauge bases on a strip, a corner and a full cube

New written construction,9September2026; Jeromie N. Beasley research programme.

## The support theorem

Consider a finite simple graph and SU(3) link Casimirs normalized byc(3)=4/3.
A Peter–Weyl spin network declares each link trivial or nontrivial. At a vertex
with exactly one nontrivial incident irrep, no invariant tensor exists. Thus
every nonzero physical spin-network support has minimum degree at least2.

Suppose every such support with at most6edges is one simple4- or6-cycle. Then
the complete physical electric subspace C<=8 consists of the constant state and
the two fundamental orientations of each of those cycles.

Proof. Every nontrivial link contributes at least4/3. C<=8 allows at most6
occupied links. At degree-two vertices gauge invariance propagates a single
irrep around a cycle, with the unique contractions. Its energy is length*c(r).
On a4-cycle c(r)<=2 admits only3,bar3; on a6-cycle c(r)<=4/3 does the same.
A higher nontrivial irrep has c>=3, hence its shortest-cycle energy is at least12.
Any other support has at least7edges and energy at least28/3. Therefore the
ENTIRE omitted space has C>=28/3. This is a universal irrep bound, not an
enumeration of a finite arbitrary irrep list. Each cycle orientation has norm1
by normalized Haar integration and inequivalent supports/irreps are orthogonal.

More generally, the nonzero pure-electric physical gap on a graph of girth g
is exactly4g/3: every nonempty admissible support contains a cycle and has at
least g links; a fundamental Wilson loop of length g attains the bound. This
uses a simple graph and uniform coefficient alpha=1. It is not an interacting
magnetic-gap theorem. At common alpha the gap is4alpha*g/3.

## Exact graph definitions and finite support checks

The scripts record every edge, cycle, face, tree and oriented Wilson word.
Their exhaustive support check tests every edge subset of size1..6, rejects
degree-one supports, and independently verifies that every remaining support is
connected and degree2. All listed graphs satisfy the hypothesis above.

| Graph | Vertices | Links | Plaquette4-cycles | All6-cycles | Complete dimension |
|---|---:|---:|---:|---:|---:|
|Two-square strip|6|7|2|1|7|
|Three-square strip|8|10|3|2|11|
|Three-face cubic corner|7|9|3|4|15|
|Complete elementary cube|8|12|6|16|45|

For the corner, label vertices by binary numbers0..6 and connect Hamming-distance1
pairs. It is the cube graph without111. For the cube include all0..7.
These are open-boundary spatial gauge graphs, NOT periodic2x2x1tori.
The cubic corner has3independent graph cycles; the cube has5, although it has6
plaquettes. The program never treats its six plaquette holonomies as independent.
It fixes one genuine graph spanning tree, leaving5independent chord matrices.
All6physical face words and all loop products are evaluated in those5variables.

The finite support enumeration proves the graph hypothesis, while the preceding
Peter–Weyl argument supplies its representation-theoretic consequence. In
particular, the45states are not a handpicked variational Wilson-loop ansatz.

## Kinetic action must precede tree contraction

A simple physical Wilson loop of k distinct links has C-eigenvalue4k/3. Two
loops sharing a link have cross derivative terms. With Hermitian generators
Tr(T_a T_b)=delta_ab/2, the exact Fierz identity is

    sum_a (T_a)_ij (T_a)_kl = (delta_il delta_jk -delta_ij delta_kl/3)/2.

The implementation differentiates the ORIGINAL link words. A positive occurrence
inserts+iT before its matrix, a negative occurrence inserts-iT after its inverse.
Two differentiated occurrences in different traces join those traces; two in
one trace split it. The diagonal contribution is4/3per occurrence. This computes
C on all trace polynomials without assuming that gauge-fixed chord Casimirs
are the original electric Hamiltonian. Tree contraction is done only afterward,
for product Haar integrals. Direct matrix-derivative controls are independent.

## Why vertex sharing is not the promised next interaction

For two edge-disjoint squares meeting at one vertex, the kinetic differential
operator has no shared-link cross derivative. On their class-function product
subspace the two one-loop Hamiltonians add independently. The full physical
space is still subject to simultaneous conjugation at the common vertex; this
statement does not replace it by a tensor product of class spaces or identify
all its excited levels with that tensor product. A common vertex can constrain
admissibility without creating a new cross term in the Hamiltonian.

Thus the external review's claim that shared-vertex coupling is automatically
the first spatially essential curvature term is not a valid general rule.
Wilson-loop curvature information already occurs on a plaquette. The new cube
calculation deliberately uses genuine shared-link interactions in all three
spatial directions, with every face and Gauss constraint retained.

A periodic direction of length1introduces a self-loop and can repeat links in a
plaquette word; length2requires distinguishing parallel oriented lattice links.
Even the ordinary length3torus has noncontractible3-link cycles. None of these
may silently inherit a simple-graph girth4argument. The local spectral-window
proof's distinct-link plaquette hypothesis must be checked on the actual cell
complex. The new certificates avoid these ambiguities by declaring open graphs.

## An analytic support lemma beyond these five finite checks

Let the spatial graph be simple, triangle-free, and contain no K_(2,3) subgraph.
Then every nonempty edge support with at most six edges and minimum occupied
degree at least two is one simple cycle, of length4,5,or6.

Proof. Such a support contains a cycle. Two separate components would need at
least eight edges. If the first cycle has length5or6, at most one extra edge
remains; a chord makes a triangle in the5cycle, and cannot be added to a6cycle
within the edge budget. An extra off-cycle edge would have a degree-one endpoint.
For a4cycle there are at most two extra edges. A chord makes a triangle. To avoid
an outside degree-one vertex, the only nontrivial addition is a two-edge path
between two cycle vertices. Adjacent endpoints make a triangle; opposite
endpoints make K_(2,3). Thus there is no permitted addition. The support is a
single cycle.

All five declared graphs are bipartite with at most two common neighbors for
any two distinct vertices; this excludes K_(2,3). Consequently their allowed
lengths are4or6. The exact support enumeration is an independent finite check
of this elementary graph argument, not the sole completeness premise.

Combining this lemma with the spin-network argument proves an all-graph-class
statement: on a finite simple triangle-free K_(2,3)-free graph, the complete
physical C<=8 space is the constant plus the two oriented fundamental Wilson
traces of every simple cycle of length4,5,or6. The entire omitted spectrum is
at least28/3. On a graph with no such cycles the retained space may be only the
constant. This theorem does not assert that the full interacting ground energy
stays in this low-electric window as graph size grows. In a periodic graph the
noncontractible short cycles must be included, even when they are not plaquettes.
