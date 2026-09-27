# Complete electric subspaces of two shared SU(3) plaquettes

Jeromie N. Beasley research programme — new reconstruction, 9 September 2026.
This is a newly written proof of the missing dependency, not a recovered original.
It applies to the actual seven-link graph and all of its physical spin-network
states. It is not a Lean formalization or a continuum construction.

## Graph, Hilbert space and normalization

The two squares share exactly one link. Suppressing degree-two vertices leaves
a theta graph with arm lengths 1,3,3. Orient all three arms from one trivalent
vertex to the other. The physical space is the vertex-gauge-invariant part of
L²(SU(3)^7,product Haar). Set C=sum_e C_e with

    c(p,q)=(p²+q²+pq+3p+3q)/3,
    c(1,0)=c(0,1)=4/3, c(1,1)=3, c(2,0)=c(0,2)=10/3.

Peter–Weyl decomposes a link into its irreducible matrix coefficients. Averaging
at a degree-two vertex forces the representations on its two links to be dual
according to orientation and contracts them uniquely. Thus a spin-network state
is labelled by irreps a,b,c on the three arms, with intertwiners in
Inv(V_a tensor V_b tensor V_c) at one end and the dual space at the other.
For multiplicity n(a,b,c), its physical multiplicity is n(a,b,c)². Its electric
energy is c(a)+3c(b)+3c(c). This supplies an exhaustive decomposition, not an ansatz
consisting only of individual Wilson loops.

The smallest nonzero Casimir is4/3; excluding 3 and bar3, the smallest is3.
The inequality follows directly from the displayed polynomial in p,q: p+q>=2
has minimum3, p+q>=3 has minimum16/3. The reps of Casimir<=10/3 are precisely
1,3,bar3,8,6,bar6.

## Exhaustive enumeration through40/3

If b=c=1, invariance requires a=1: the constant state.
If just one long arm is trivial, a is dual to the other long arm; its energy is
4c(b). Through40/3 this produces the four oriented fundamental square loops
(energy16/3), the two adjoint square loops (12), and the four sextet/antisextet
square loops (40/3).

If a is trivial and both long arms are nontrivial, they are dual. Their energy
is6c(b), so through40/3 they must be fundamental, giving two rectangle states
of energy8. Notice that the rectangle has six occupied links, not eight.

If all arms are nontrivial and either long arm is not fundamental, its energy
is at least 3*3+3*(4/3)+4/3=43/3, beyond the proposed cutoff. Hence both long
arms are fundamental or antifundamental. The exact tensor rules are

    3 tensor3=6 direct-sum bar3,
    bar3 tensorbar3=bar6 direct-sum3,
    3 tensorbar3=1 direct-sum8.

Taking the necessary dual on the short arm gives two baryonic states at28/3,
two short-arm adjoint states at11, and two short-arm sextet states at34/3.
Every listed intertwiner multiplicity is1. There are no remaining cases.

| Energy | New states | Cumulative dimension |
|---:|---:|---:|
|0|1|1|
|16/3|4|5|
|8|2|7|
|28/3|2|9|
|11|2|11|
|34/3|2|13|
|12|2|15|
|40/3|4|19|

Consequently the complete physical cutoffs at8,12,40/3 have dimensions7,15,19,
with entire omitted electric sectors bounded below by28/3,40/3,43/3 respectively.
The final floor is attained: 8 tensor3 contains3, so one long adjoint arm, one
long fundamental arm and a short antifundamental arm give43/3. A diagonal Casimir
estimate controls infinitely many irreps; no irrep outside the table is silently
truncated.

## Trace basis and the saved matrices

After a spanning-tree gauge fixing choose square variables U,V with the relative
orientation used by the earlier programs. The rectangle is Tr(U V†). The seven
initial basis functions are1,TrU,TrU†,TrV,TrV†,Tr(UV†),Tr(VU†).

Put f=TrU TrV and g=Tr(UV). The added baryonic functions f-g and its conjugate
have squared norm4/3; f+g and its conjugate have squared norm8/3 and the sextet
energy34/3. The two short-arm adjoint functions are
TrU TrV†-Tr(UV†)/3 and its conjugate, with squared norm8/9. The single-square
adjoints |TrU|²-1 and |TrV|²-1 and the four characters
chi6(U)=[(TrU)²+Tr(U²)]/2 and their conjugate/V analogues have norm1.

Haar orthogonality and the fundamental Fierz identity verify these norms and
eigenvalues; the earlier independent Gell-Mann differential checker supplies
an implementation cross-check. The representation count above, together with
these independent functions at the corresponding energies, proves completeness.
It is not inferred merely from the functions being orthogonal.

For this nonunit-normalized extended basis retain its Gram G. If S and S2 are
matrix elements of ReTrU+ReTrV and its square, then the coupling quadratic form is

    M=S2-S G^(-1) S.

The physical Hamiltonian quadratic form is diag(E_i+6lambda)G-lambda S.
Congruence by the Gram isometry preserves inertia. The old19-state verifier
therefore uses the correct finite quadratic forms once the above analytic
completeness and the accompanying allocation proof are supplied.

A previous file named TWO_PLAQUETTES.md was not recovered. This reconstruction
is explicitly new. It does not retroactively add a Lean proof to the old result.
