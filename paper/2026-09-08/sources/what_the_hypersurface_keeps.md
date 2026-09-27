# What the Hypersurface Keeps

### The holonomy argument, assembled from the operator-first corpus

*Jeromie N. Beasley — 8 September 2026 — working draft, built from UPG v2, FOFT v2, Matter v5, the ladder paper, the sofic note, Light Edition 4, and the offset paper v27/v30*

---

## 0. The claim, in one sentence

A hypersurface does not store a value. It stores a **record that is locally constant under every deformation preserving the arrangement, and changes only on a discrete wall set** — and that is what "keeping the phase" means in every paper of this corpus, in four different mathematical categories.

The purpose of this note is to show that this is one theorem wearing four costumes, to say precisely where it is proved and where it is analogy, and to name the wall set in each case. Nothing here is a new claim about physics. It is a claim about which existing results are the same result.

---

## 1. Why holonomy, and not "the boundary remembers"

"The boundary remembers" is a slogan and cannot be graded. Holonomy can. A holonomy statement has three parts, and every one of them is checkable:

1. **A record** — a number attached to a closed arrangement.
2. **An invariance** — a class of deformations under which the record does not move, exactly and at any strength, not merely to leading order.
3. **A wall set** — the complementary class, where the record does move, and the order at which it starts moving.

A result that supplies all three is a holonomy result. A result that supplies only the first is a measurement. This is the standard the rest of the note applies, and by it several things in the corpus that sound like holonomy are not, and one thing that was never called holonomy is the cleanest instance of it.

UPG states the requirement in exactly this form, as an axiom on admissible bulks: the boundary record is **locally constant in the holonomy parameters, with jumps confined to a discrete wall set**, and the total record is minimal, |n_total| = 1. That is Definition 3.1, clauses (4) and (5). Everything below is an instance of, or a failure of, that definition.

---

## 2. The four instances

### 2.1 UPG — the winding currency (the original)

UPG denominates every topological claim in three integers: **index, spectral asymmetry, and winding**. The winding is the loop integral of the gauge-invariant angular velocity on the holonomy torus, and it is an exact integer — 0 for non-enclosing loops, +1 per enclosure, +2 for a double loop, verified to 10⁻⁶. Its self-adjoint ancestor is the Levine–Tristram signature σ_K : S¹ → ℤ, an integer step function whose plateaus jump exactly at the Alexander roots on the holonomy circle.

Record: the winding integer. Invariance: any deformation of the holonomy parameters within a plateau. Wall set: the Alexander-root locus. **All three parts present; graded [T] in the source.**

The noncommutative anchor of §4.4 is the same currency evaluated on a non-smooth holonomy: replace the two commuting holonomy coordinates by two unitaries failing to commute by a scalar, and the integer record survives with a stated domain of validity. Its literature name is the Exel–Loring invariant, equivalently the Bott index, and on a lattice two-torus it equals the Chern number under short range, boundedness and gap. That the same integer is reachable by a smooth and a noncommutative route is the strongest single piece of evidence in the corpus that the record is a property of the *arrangement* and not of the coordinates chosen to describe it.

### 2.2 The offset paper — the cleanest instance, and it was never called holonomy

This is the case where all three parts are proved rather than measured, and it is the newest.

**Record.** Tr K_A, the trace of the single-particle entanglement Hamiltonian on a region. Not a bulk quantity: it is the difference of two cut-localised charges, Q_L − Q_R, and it vanishes exactly when the two cuts sit at the same phase of the unit cell.

**Invariance.** Theorem 10 of the offset paper: if an operation S fixes the state, acts on correlations as particle–hole, and maps the block to itself, then the correlation spectrum is symmetric under ν ↦ 1−ν and Tr K_A = 0 **exactly** — for every block length, at every precision, with no reference to a gap. On the Rice–Mele chain S = P∘R, particle–hole conjugation composed with bond-centred reflection; the family is wider than that, since the odd-in-k mass substrate breaks reflection and time reversal separately and still gives the exact zero under P∘R∘T.

The invariance is not asymptotic and not perturbative. An S-even deformation of the cut arrangement leaves the zero at the forty-digit floor at δ = 0.01, 0.1, 0.5 and 1.0 — the last equal to the strong hopping itself. The arrangement is deformed as hard as the chain and the record does not move.

**Wall set.** Exactly the S-odd deformations, and they move the record at *first* order: ∂Tr K_A/∂δ = 0.5070 for a single site, 1.0140 for its mirror-symmetric pair — exactly twice, because a single site is half an S-even pattern plus half an S-odd one. The response is not screened: it grows with depth into the block, 0.507 → 4.671 from cut to centre, mirror-symmetric about the centre bond. That is the sharpest distinction in the corpus between the two halves of K_A: **the trace-free part is local and screened; the trace part is protected by a symmetry of the arrangement and is not local at all.**

Record, invariance, wall set — all three, all proved. By the standard of §1 this is the corpus's holonomy theorem, and the offset paper does not use the word.

**The phase is literally an angle.** Tr K_A = gd⁻¹(χ) and 1/ξ = gd⁻¹(ψ): the zero and the logarithm of the span are the same inverse Gudermannian of two angles, joined by the mass angle θ through tan(χ/2) = cos θ √(tan(ψ/2)). And the ladder phase α_ε = ¼ + F(φ|ũ²)/4K(ũ²) is an **incomplete elliptic integral of the first kind** — an Abel map on the curve whose periods give the spacing. A phase accumulated along a path on a curve, invariant under the deformations preserving the arrangement, is not a metaphor for holonomy; it is the definition.

### 2.3 FOFT — the holonomy phase integral, and an honest separation

FOFT contains a genuine holonomy phase: the flat-torus phase form dΦ = d arctan(Y/X) along the sweep X = 1, Y = xt accumulates Φ(x) = arctan x, and integrating against the scale weight gives **Catalan's constant** G = ∫₀¹ λ⁻¹ arctan λ dλ, verified to thirty digits, graded [T]+[V].

The reason this entry matters is the correction attached to it. The paper is explicit that the holonomy constant and the **ledger constant are distinct invariants of distinct objects**: the ledger integral is π²/6, not G, and the earlier identification of the two was wrong and was withdrawn. That is the discipline this note is trying to preserve. Two constants arising from the same apparatus are not the same invariant unless the objects coincide, and here they demonstrably do not.

### 2.4 Arithmetic Kakeya — the same invariance over the integers

The GL₂(ℤ) matrices fixing the forbidden line form two one-parameter families, and relabelling a forcing pair by any of them produces a forcing pair with **identical m, n, |R| and |T|** — hence identical score. An infinite orbit at constant record.

Record: the score. Invariance: the integer symmetry group of the arrangement. Wall set: relabellings that do not fix the forbidden line. Same three parts, in a category with no geometry in it at all — which is the best evidence that the statement is about arrangements rather than about physics.

---

## 3. The second currency: spectral asymmetry, and where it disagrees

UPG's three currencies are index, **spectral asymmetry η**, and winding. The offset paper measures an η independently and finds something that ought to be recorded here, because it is a genuine disagreement rather than a confirmation.

For odd blocks, η(K_A) is the sublattice imbalance of the block — +1 when it holds one more A site than B, −1 the other way, 0 when even — and it is fixed by which sublattice the *left cut* exposes. The **sign** of Tr K_A, by contrast, follows L mod 4. These two are independent ℤ₂ labels and they disagree: η never moves while the trace changes sign.

So the boundary carries **two independent ℤ₂ records plus one non-integer amplitude**, 2 artanh(v/√(E_min E_max)). That is more structure than UPG's currency list anticipates, and it is a place where the offset paper's measurement constrains the framework rather than illustrating it. The mechanism of the sign is a theorem — a one-site shift of an odd block mirrors its whole spectrum — while the growth-by-one-cell rule is measured, not proved.

---

## 4. What the census contributes: the price of a direction

The span side supplies the other half of the picture, and it is what makes "the boundary keeps a record" quantitative rather than qualitative.

The census counts resolvable rungs against a resolution floor: N = 2Λ/Δ per cut, with the ladder spacing Δ = 4πK(ũ)/K′(ũ) and Δ log(8ξ) → 2π². The counting coefficient is **A = 2c/π²**, carrying the central charge — confirmed at two central charges, c = 1 and, by a direct rung count on the transverse-field Ising chain, c = ½. The same ladder read with the other calibration returns Calabrese–Cardy, S = log(8ξ)/6 per cut: the π² survives in the census because it counts rungs against a floor, and cancels in the entropy because it weights them.

The consequence for this note: a hypersurface's capacity is **logarithmic in resolution, not proportional to area** — it grows as log ξ · log(1/ε). That is the honest statement of what a boundary can hold, and it is also the fence: the census does not scale as an area, so no area-law identification follows from it automatically.

---

## 5. What this does *not* establish

Stated once, plainly, because the argument is worth more with the fence than without it.

- The Rice–Mele results are one-dimensional free fermions. There is no interacting result, and Tr K_A is not even defined for an interacting substrate until the embedding is named.
- The metric in this corpus is intrinsic to a projector bundle. It is not a spacetime metric, and no substitution of one for the other is made or implied.
- The census grows as log ξ log(1/ε). It is not an area, and nothing here derives a cosmological magnitude. The comparison to Einstein's 1919 trace removal is structural — what role a term proportional to the identity plays inside a derivation — and is graded [H] wherever it appears.
- The full offset formula remains recognised, not derived: the endpoint asymptotic |a_N| → |v|/√(E_min E_max) is open, and the exact reductions around it are what is proved.
- Suns, black hole, gravity and price-of-a-direction were **not available in this session**; their hypersurface results are therefore not represented above, and the corresponding sections are owed rather than written.

---

## 6. The one-line summary

Across a knot complement, a lattice two-torus, a noncommutative anchor, an entanglement cut, and a labelled graph over the integers, the same structure recurs: **a record attached to an arrangement, exactly invariant under the deformations that preserve the arrangement's symmetry, moving at first order only on a discrete wall set.** In UPG it is an integer winding with the Alexander roots as its walls. In the offset paper it is a boundary charge with the S-odd deformations as its walls, and there all three parts are proved. In Kakeya it is a score with an infinite GL₂(ℤ) orbit at constant value.

The phase keeps the message because the message was never in the interior to begin with — it is in how the cuts sit against each other, and that is exactly the quantity a holonomy is built to measure.
