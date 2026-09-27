# Coarsen the spectral record without discarding the direction of the inequality

Jeromie N. Beasley research programme, 9 September 2026. Written finite operator
comparison, supported by the same full-hidden-floor proof as RESOLVED_BOUNDARY.
Not a priority claim for scalar convexity or spectral quadrature.

The energy-resolved positive coupling matrices M_e contain more information than
their sum M. Sometimes not all of their individual labels need to be kept at full
resolution to certify a desired, slightly weaker, margin. The appropriate coarse
record is NOT just a mean energy. A mean substituted into an inverse gives the
wrong inequality direction for an upper self-energy penalty.

## Exact one-sided coarsening

Suppose s>0, t=E_*-z and s*a+t>0. In one bin let a<=e<=b. Set
x=s*e+t, x_a=s*a+t, x_b=s*b+t. Exact algebra gives

    (x_a+x_b-x)/(x_a*x_b) - 1/x
       = (x-x_a)*(x_b-x)/(x_a*x_b*x) >= 0.

This includes a=b: its contribution is exact. Thus, for positive matrices M_e,

    sum_bin M_e/(s*e+t)
      <= [(s*(a+b)+t)*M0 - s*M1]/[(s*a+t)*(s*b+t)],
    M0=sum_bin M_e,  M1=sum_bin e*M_e.

Every scalar weight on the upper side is a positive chord of 1/x. Summing
positive-weight matrix inequalities needs no commutativity between the M_e.
The chord is at most 1/(s*a+t), hence no worse than using the first omitted
energy for the entire coupling. Between these two extremal descriptions,

    resolved penalty <= binned penalty <= global-floor penalty.

Together with D>=s*C_Q+E_* and z<d, this gives

    A-z-global_penalty <= A-z-binned_penalty
      <= A-z-resolved_penalty <= the true Schur complement.

Any binned lower Schur matrix with n-1 strictly positive directions, together
with the same verified negative direction of A-z, supplies the same full-tail
counting argument. The binning does not change r, the model, or the physical
basis. Its upper bound does not assert that the actual D has only these poles.

## Executed bounded examples

These two cases use allocations and local-floor certificates from accepted
resolved targets, but use a deliberately lower z to test a smaller description.
Each example checks the exact scalar chord identity for every energy, verifies
both matrix-order differences by rational PSD elimination, and checks three
outward-interval inertias at r and z.

- The 12-link cube, alpha=lambda=1: three consecutive energy bins replace the
  eleven positive residue matrices by six moment matrices and certify gap>=2.
  The parent, unbinned certificate is stronger: gap>=2.109917.
- The 20-link two-adjacent-cube graph, alpha=1, lambda=1/2: two consecutive bins,
  four moment matrices, certify gap>=7/2. The parent bound is3.817691.

These improve on the corresponding aggregate-floor bounds1.649349 and3.295750,
respectively, but are weaker than the full energy-resolved results. This is a
certified loss of resolution, not a new fastest-runtime claim or extra physical
observations. The current implementation still constructs all residues before
forming moments; a direct-moment constructor is a separate optimization.

The native eye retains missing/inapplicable status on other models rather than
extrapolating these two examples. The full report stores all matrix witnesses.

## Negative control: averaging before inversion

With two unit masses at energies10 and14 and test point0,

    1/10 + 1/14 = 6/35 > 1/6 = 2/12.

The difference is1/210. Replacing both energies by their mean would underestimate
the penalty, which can falsely certify a gap. Positive chord coarsening keeps the
information needed for a one-sided bound. This is precisely the extra condition
an eye must carry when changing the resolution of its combined output.
