# The Kakeya dual theorem on the actual gauge matrices

Jeromie N. Beasley research programme — 9 September 2026.

## Reused theorem and its direction

The exact source is `OperatorFirst/KakeyaForcingLinear.lean`, commit
`41fbf3b9e6ad8143d597928e477a9d94adb6d6d6`, in PR #4. In that source

    CanForce(T,b) means there exists x with T x=0 and b x !=0.

The declaration `dual_certificate` proves that b=y composed with T excludes
CanForce(T,b). Thus a dual row proves absence of an invisible target-changing
vector; it does not prove the opposite. The theorem is general finite linear
algebra over a field. Its reuse is not a new Kakeya exponent or an identification
of a constructible arithmetic graph with a gauge lattice.

Source: https://github.com/dicipler-pixel/operator-first/blob/41fbf3b9e6ad8143d597928e477a9d94adb6d6d6/OperatorFirst/KakeyaForcingLinear.lean

## An actual rational instance

For each of the five finite gauge graphs in this session let A be the retained
Hamiltonian at alpha=lambda=1, M the exact omitted-coupling Gram, and e0 the
constant electric-vacuum basis vector. The exact computed M has kernel span(e0).
For the target b(x)=x0, M e0=0 and b(e0)=1. Therefore CanForce(M,b) holds: a
single direct boundary reading cannot determine that coordinate.

Set Theta x=(M x,M A x). The source code constructs rational rows y0,y1 such that

    y0 M + y1 M A = e0^T.

Every component of this identity is checked exactly. Applying the pinned
`dual_certificate` to the row y=(y0,y1) gives not CanForce(Theta,b).
This is a direct application with explicit matrices, target, and witness—not
only an analogy involving equal dimensions or a numerical rank.

To construct the rows, choose j with (M A)_(j,0) !=0 and set

    y1 = e_j^T/(M A)_(j,0).

Then b-y1 M A vanishes in coordinate0. Since the non-vacuum block of M is
positive definite, exact rational elimination solves y0 M=b-y1 M A with
(y0)_0=0. The independent code checks the final row identity from scratch and
rejects a deliberately corrupted entry. Across dimensions7,11,15,45,95 this
checks173 scalar equalities and five corrupted-certificate controls.

## Relation to the observability eye

The positive-Gram identity

    ker(M+A M A)=ker M intersect ker(M A)

is equivalent to the relevant kernel statement, since ker M=ker sqrt(M).
The computed first matrix has rank n-1; M+A M A has rank n. Directly invisible
is therefore not invariant under the retained generator. The explicit dual
row is stronger evidence about the named target than a bare statement of rank.

Theta is an algebraically defined retained-generator map. It is not silently
identified with the measured derivative of an open system when unknown hidden
initial data provide a forcing term. Nor does retained observability prove that
B sees every state of the infinite hidden space. The independent hidden-dark-
eigenvalue control still applies.

## Formal and numerical scope

The general dual theorem has its earlier pinned Lean source. Its five new gauge
instances are exact Python rational calculations and a new native observer;
there is no new Lean compilation of the173 numerical identities. The separate
12-declaration closing-step Lean module has its own, narrower verification
record. Neither gives a continuum gap by itself.

Correction record: an earlier prose count said171; the actual dimensions sum to173. The executable matrices, row identities, and stored results have not changed.
