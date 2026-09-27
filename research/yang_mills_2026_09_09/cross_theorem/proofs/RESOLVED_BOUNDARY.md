# Energy-resolved boundary certificates: the usable Light-to-Yang–Mills bridge

New application and written derivation,9September2026; research programme of
Jeromie N. Beasley. The Schur/Feshbach, positive-weight and representation tools
are established mathematics. No priority for their general forms is asserted.

## 1. Retain the energy labels as well as the boundary Gram

On a finite gauge graph write H=alpha C+lambda(3p-S), where S=sum_faces ReTrU_p.
P=1_[0,R](C) is the COMPLETE physical electric cutoff and Q=I-P. In this note
alpha=1; a common energy rescaling restores alpha afterward. In the split
H=[A B;B* D], B=-lambda P S Q. The preceding allocation proof gives

    D >= T=s C_Q+E_*, d=s c_+(R)+E_*, s>0.

For z<d, the inverse order inequality gives

    0 <= B(D-z)^(-1)B* <= B(T-z)^(-1)B*.                (1)

For completeness, inverse order follows from
<x,A^(-1)x>=sup_y[2Re<x,y>-<y,Ay>] for strictly positive self-adjoint A;
a larger quadratic form has a smaller supremum. This argument also applies
to closed unbounded forms. D and C_Q need NOT commute.

Because multiplication by a finite Wilson trace sends a finite electric
subspace to only finitely many Peter–Weyl irreps, Ran(QSP) has finite Casimir
support. Let E_e be the full Casimir spectral projections and put

    M_e=P S Q E_e Q S P >=0,    M=sum_e M_e.

The exact comparison self-energy and Schur lower matrix are

    Sigma_upper(z)=lambda² sum_e M_e/(s e+E_*-z),
    K_res(z)=A-z I-Sigma_upper(z).                      (2)

They obey

    A-z-M*lambda²/(d-z) <= K_res(z) <= S_exact(z) <= A-z. (3)

Indeed e>=c_+(R) for every omitted component, so each positive M_e has a
smaller or equal penalty than in the scalar-floor bound. If K_res(z) has
m-1strictly positive directions and A-z has a negative direction, the exact
Schur matrix has precisely1negative direction and no zero. The full operator
then has exactly1simple eigenvalue belowz and z is in its resolvent. A certified
variational E0<=r<z yields gap(H)>=z-r. This is the same vacuum-free logic as
continuation Theorem3, with a stronger upper self-energy rather than a new
unproved vacuum identification.

The scalar-floor term is already MATRIX-support retaining (M, not ||B||²I).
This improvement is a second refinement: do not discard which energies belong
to the directions making up that matrix.

## 2. Exact finite energy support without truncating the hidden Hamiltonian

Each basis loop and face loop traverses each physical link at most once.
Their product places on a link one fundamental/antifundamental, two equal
orientations, or two opposite orientations. The allowed Casimirs are respectively
{4/3}, {4/3,10/3}, or {0,3}, by3tensor3 and3tensorbar3. Adding over ORIGINAL links
gives a finite, possibly overcomplete list of energies for that product.
For these known distinct energies the Lagrange polynomial

    L_e(C)=product_{f!=e}(C-f)/(e-f)

is exactly the relevant Casimir spectral projection on that polynomial.
The original-link Fierz operator calculates L_e(C) without diagonalizing a
truncated physical Hamiltonian. Exact Haar inner products give every M_e.
The checks verify C L_e f=e L_e f, sum_e L_e f=f, orthogonality, positivity,
and sum_{e>R}M_e=P S²P-(PSP)². Low-energy components are reconstructed in P.
The complete P proof comes from SPATIAL_BASES.md, not just that last test.

This is the finite-pole/moment discipline used in the Light/elemental corpus:
recover each positive contribution BEFORE applying its distinct frequency or
energy denominator. The support bound is proved here for C, so the recovery has
its required finite-domain premise. The magnetic hidden operator D is not being
claimed to preserve this finite space.

## 3. Relation to physical memory, and a prohibited shortcut

The ACTUAL hidden-sector spectral measure is dmu_D(t)=B dE_D(t)B*. It gives

    memory(t)=B exp(-itD)B*,
    Sigma_exact(z)=integral (e-z)^(-1) dmu_D(e), z below D.

The hidden initial-state force must be retained in a time evolution. These are
the exact eliminated-sector objects in the light and elemental papers.
By contrast, the finite M_e above are Casimir-resolved components of a positive
COMPARISON operator. Equation(1)is an inequality, not Sigma_exact=Sigma_upper.
No finite-pole claim for the full interacting D follows. Nor does D>=T imply
exp(-tD)<=exp(-tT) in general: the matrix exponential is not operator monotone.
The usable transferable object is the ordered resolvent bound.

Below the hidden spectrum, for z1<z2,

    [Sigma_exact(z2)-Sigma_exact(z1)]/(z2-z1)
      =B(D-z2)^(-1)(D-z1)^(-1)B* >=0.

Its kernel is exactly ker B*: a strictly positive scalar function of D has no
kernel, so a vanishing quadratic form forces B*x=0. This is the same positive
weighted-nullspace reasoning as Light Corollary4.4 and Elemental Proposition4.
It detects coupling silence, not absence of a hidden physical excitation.

## 4. Rank alone still does not supply a gap

For A=diag(0,2,4), d=3,z=9/5, compare M1=diag(0,1,0) and M2=diag(0,0,1).
Both have rank1, trace1 and identical eigenvalues. K_M1 has2negative eigenvalues;
K_M2 has1. Their ranges meet different retained energies. This is the precise
use of the Kakeya lesson: equal rank is not equal relation space or equal
ability to meet a target. Retain the actual subspace/dual witnesses.

Even every boundary-coupled mode can miss an excitation. Set A=diag(0,2),
D=diag(1/10,10), and let B have its only nonzero entry B_(2,2)=1/10. The hidden
1/10mode is dark at the boundary but is a real full excitation. Using the
coupled energy10as the WHOLE omitted floor would falsely certify a gap near1.
The correct requirement z<d applies to every hidden state, including kerB.
The scanner explicitly refuses that replacement.

## 5. Scope of the new spatial result

The small three-plaquette strip, corner and full cube are actual connected
spatial gauge Hamiltonians. Their entire representation tails are controlled
by the support theorem, allocation and(1). The finite boundary decomposition
allows stronger certificates at the SAME retained dimension. No statement of
uniformity in cube count, physical volume or a->0is supplied by those finite
examples. The existing local-window theorem remains a different transfer tool
for a product local cutoff; its error must be paired with a compression gap
for the SAME operator and cutoff, not with a gap borrowed from this small cube.
