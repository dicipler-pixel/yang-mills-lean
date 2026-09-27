# Two further finite corollaries: parameter stability and pole degree

Jeromie N. Beasley research programme — 9 September 2026.
These are written corollaries, not additional large-lattice computations.

## A genuine interval in magnetic coupling, at fixed spatial graph

Write H(lambda)=alpha C+lambda V, with V=sum_p(3-ReTrU_p), and fix alpha.
For SU(3), -3/2<=ReTrU<=3, hence0<=V<=(9/2)P I where P is plaquette count.
The variational principle gives, for delta>=0,

    E_j(lambda)<=E_j(lambda+delta)<=E_j(lambda)+(9/2)P delta.

It follows in both directions that

    gap(lambda+delta)>=gap(lambda)-(9/2)P |delta|.

One may equivalently center V and use its bounded perturbation norm. This
controls the entire finite-graph Hilbert space, not just the retained matrix.
For the cube, P=6 and the exact certificate at alpha=lambda=1 is2109917/1000000.
Consequently, at any alpha>0 with19/20<=lambda/alpha<=21/20,

    gap(H)>=alpha*(2109917/1000000-27/20)
          =alpha*759917/1000000>0.

This is a conservative parameter interval on the SAME twelve-link graph.
It is not a theorem uniform over expanding spatial volumes or a continuum
trajectory. The alpha rescaling is H=alpha[C+(lambda/alpha)V]. The dimensional
coefficient alpha carries the chosen energy units; no GeV or frequency is fitted.

## The boundary-column degree mechanism controls a rational determinant

Let M_e be the exact positive residue matrices in the energy-resolved comparator,
and r_e=rank M_e. For any fixed matrix A(z), the polynomial

    det(A(z)-sum_e t_e M_e)

has degree at most r_e in the independent variable t_e. To prove it, choose an
invertible change of basis putting the range of M_e into r_e coordinates, or
write a rank factorization M_e=X_e Y_e. Determinant multilinearity cannot choose
more than r_e independent columns from that perturbation. All other variables
are held arbitrary throughout, so this is a multidegree statement.

On substitution t_e=lambda²/(s e+E_*-z), the product

    product_e(s e+E_*-z)^(r_e)

is therefore a sufficient common denominator for the determinant. Additional
cancellation can lower it, so it is not asserted minimal. The source mechanism
is the finite/all-size column-support degree theorem used in the user's
Offset/Laurent-boundary line. Its special Rice–Mele invariants and sine law are
not imported to this gauge Hamiltonian.

The exact positive-semidefinite elimination of each computed M_e gives the
following summed-rank denominator bounds:

| Model | Sum of residue ranks | Dimension times number of poles |
|---|---:|---:|
| Two squares |16|49|
| Three-square strip |46|110|
| Three-face corner |59|150|
| Full cube |259|495|
| Vertex-wedge control |9|15|

This is an algebraic reduction, not a measured runtime gain or an executed
Sturm certificate over the whole coupling axis. It provides a concrete input
for a future interval-in-energy determinant certificate and identifies when a
one-column simplification is unavailable.
