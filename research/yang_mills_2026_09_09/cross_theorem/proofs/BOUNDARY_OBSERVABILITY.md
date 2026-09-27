# A silent boundary direction can become visible after one retained step

Jeromie N. Beasley research programme — 9 September 2026.

This is a finite linear-algebra bridge between the Light paper's warning about
one-energy/probe records and the arithmetic Kakeya work's exact-span discipline.
It is not a map identifying a Kakeya forcing graph with a gauge lattice.

Let A=A† act on the retained n-dimensional space and M=BB†>=0. The directly
silent retained space is ker M=ker B†. Define

    O_k=sum_(j=0)^k A^j M A^j.

Every summand is a positive Gram. Therefore

    ker O_k=intersection_(j=0)^k ker(B† A^j).

The orthogonal complement is the span of A^j ran B for0<=j<=k. Cayley–Hamilton
shows that k=n-1 suffices for stabilization. Its orthogonal complement is an
A-invariant subspace that does not couple to the omitted sector. Its eigenvalues
still belong in a gap count; invisibility does not remove a physical eigenstate.

The proof is to evaluate a quadratic form:

    <x,O_k x>=sum_j ||B† A^j x||².

A sum of squares is zero precisely when all the squares vanish. Multiplication
of the characteristic polynomial of A expresses all higher powers through the
first n, proving stabilization. These are established observability/Krylov
ideas, not a claim to have invented them. The source-specific contribution is
to use their exact version as a guard in the same certified gauge calculation.

## Actual gauge result

In every newly tested C<=8 model (two squares, three-square strip, three-face
corner, full cube, and vertex-wedge control), exact outward LDL proves the
non-vacuum block of M strictly positive. The first row and column are zero.
Thus ker M is precisely the constant electric-vacuum line.

At lambda=1, exact computation gives <0,A M A0>>0, and O_1=M+A M A is strictly
positive on the entire retained space. The directly silent line is therefore
NOT an invariant decoupled eigenstate: retained dynamics sends it into visible
plaquette directions. For the45-dimensional cube, the direct boundary rank is44
but the two-step retained observability rank is45.

This distinguishes three objects that a single rank can conflate: the direct
omitted-coupling support, the retained reachable/observable span, and the full
infinite-dimensional physical Hilbert space. The calculation proves completeness
of that retained observation only. It does not prove that B sees every state in
Q, and the independent uncoupled-hidden-mode counterexample remains necessary.

## Why the Kakeya comparison is useful and limited

The arithmetic work asks for membership in an exact relation space after adding
the known-coordinate space. Its terminal dual witness certifies non-membership.
Here, membership is in an exact Krylov span and a vector in the displayed kernel
is the dual obstruction. Equal dimension or equal singular values do not say
which target is in the span. The exact-space bookkeeping and positive-Gram kernel
identity transfer; the arithmetic construction rules and its score do not become
an energy inequality for Yang–Mills.
