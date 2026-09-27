# Scaling controls and the fixed-total-cutoff obstruction

Jeromie N. Beasley research programme — new reconstruction, 9 September 2026. This supplies the missing exposition for the existing exact scaling calculator; it is not a recovered original document, a derived renormalization trajectory, or a continuum Yang–Mills construction.

## Exact size of a single-link cutoff

The Peter–Weyl dimension retained at p+q<=N is

    D(N)=(N+1)(N+2)^2(N+3)^2(N+4)(3N^2+15N+20)/2880.

Indeed, writing t=s+2, the squared SU(3) representation dimensions on shell s sum to

    sum_(p=0)^s [(p+1)(s-p+1)(s+2)/2]^2 = (t^7-t^3)/120.

Expand j^2(t-j)^2 and apply the finite sums of j^2,j^3,j^4 to get sum_(j=1)^(t-1) j^2(t-j)^2=(t^5-t)/30. Multiplication by t^2/4 gives the shell formula. The displayed D has D(0)=1 and polynomial difference D(N)-D(N-1)=((N+2)^7-(N+2)^3)/120, which proves the total by telescoping. A small shell index therefore still allows a large local Hilbert space; tensor products grow much faster.

## A declared simultaneous scale family with vanishing truncation error

Fix an integer R>=1 and integer h>=2. Set

    a=2^(-h), alpha=2^h/h, lambda=h*2^h,
    omega=1, M=3R^3*2^(3h), N=16h.

This is a deliberately declared stress family for the written local-window theorem. No identification with the Yang–Mills renormalization flow is made. The periodic cubic graph has four incident plaquettes per link, so its recurrence uses b=9lambda and denominator delta_k=alpha*c(k+1)-12lambda-1.

For k>=10h, c(k+1)>=k^2/4 gives

    delta_k >= 13h*2^h-1 >= 12h*2^h,
    b/delta_k <= 3/4.

Since every earlier epsilon is at most one, iteration through k=10h,...,16h gives epsilon_N<=(3/4)^(6h+1) and epsilon_(N-1)<=(3/4)^(6h). Thus

    S=M epsilon_N^2 <= (27/16) R^3 (531441/2097152)^h,
    K=9lambda M epsilon_(N-1)epsilon_N
      <= (81/4) R^3 h (531441/1048576)^h.

Both bases are strictly smaller than one. In particular, the second is smaller than3/4, and for h>=4 the successive ratio of h(3/4)^h is at most15/16. Therefore S and K tend to zero, S<1 eventually, and the sufficient error (S+K)/(1-S) tends to zero at fixed R.

This proves that this particular representation-cutoff error can be controlled along the declared family. It does not prove that the compression gap stays positive, that observables converge to a nontrivial quantum field theory, or that R can be sent to infinity without additional uniform estimates.

## Why shifting an extensive vacuum does not repair a crude floor

For every d,r,c, (d-c)-(r-c)=d-r. A common scalar shift cannot make the absolute omitted-sector denominator exceed a variational ground endpoint if it did not before.

A concrete counterexample to confusing failure of that comparison with gaplessness is the product of two-level systems

    h = [[1,-1],[-1,2]] = diag(0,1) + [[1,-1],[-1,1]].

The potential is nonnegative. The exact one-site eigenvalues are (3-sqrt5)/2 and (3+sqrt5)/2. On M sites the ground energy is M(3-sqrt5)/2 while the excitation gap remains sqrt5. A fixed total-electric cutoff of four has bare omitted floor5; since (3-sqrt5)/2>3/8, already M=14 makes E0>5. The bare global-floor certificate then cannot reach the actual vacuum even though the gap is unchanged and positive.

The one-site ground overlap with the electric vacuum is p=(1+1/sqrt5)/2<3/4. The mass of the product ground state in any fixed total-electric cutoff N is a fixed-degree binomial sum bounded by a polynomial in M times p^(M-N), hence tends to zero. A fixed-total-excitation basis can therefore lose the interacting vacuum as volume increases. This is an explicit product-model obstruction to a method, not a theorem that the interacting gauge theory is gapless.

## Verification scope

The inherited scaling_controls.py checks the exact dimension formula, recurrence envelope inequalities and malformed inputs with rational arithmetic. The all-h arguments are the elementary inequalities and telescoping proof above, not an extrapolation from a finite numerical table. The local-window operator hypotheses remain those in LOCAL_WINDOW_AND_GAP_TRANSFER.md. Nothing in this note supplies a compression gap for a different graph or cutoff.
