/-!
# The 28/3 electric tail floor on the SU(3) test graphs

Layers 1 and 3 of the floor argument in
`research/yang_mills_2026_09_09/cross_theorem/proofs/SPATIAL_BASES.md`.

* Layer 1 (proved): single-irrep Casimir bounds from c(p,q) = (p²+q²+pq+3p+3q)/3.
* Layer 3 (proved, finite check): on each graph, every link support with at most
  six links and no vertex of support-degree one is a single connected 4- or 6-cycle.
* Layer 2 (NOT proved, not formalized): the SU(3) step, here called the gauge support rule: Peter–Weyl / gauge invariance, i.e. a physical
  spin-network support has no vertex of degree one, and a cycle carries one irrep.

`SmallSupportsAreCycles g` is the purely graph-theoretic Layer 3 property, proved below;
it says nothing about SU(3). The gauge support rule (Layer 2) is still open.

Combining: any admissible support state with energy above 8 has energy ≥ 28/3.
Conventions: α = 1, open-boundary graphs. Core Lean only.

Coverage: two squares, three-square strip, three-face corner and cube are checked here by
`decide +kernel`. The double cube (20 links) is checked in `TailFloorDoubleCube.lean`:
the fused checker `checkB` and `checkB_sound` are proved here, and that file splits
`checkB dcubeE = true` into 328 small kernel lemmas (a single `decide +kernel` call
exhausted about 11 GB). 47 admissible supports (11 squares, 36 hexagons), matching
independent Python counts.
-/

namespace TailFloor

/-! ## Layer 1: Casimir bounds (scaled by 3: c3 p q = 3·c(p,q)) -/

def c3 (p q : Nat) : Nat := p*p + q*q + p*q + 3*p + 3*q

theorem c3_fund : c3 1 0 = 4 ∧ c3 0 1 = 4 := by decide
theorem c3_adj : c3 1 1 = 9 := by decide
theorem c3_31 : c3 3 1 = 25 := by decide   -- 25/3 < 28/3: the single-link value below the floor
theorem c3_40 : c3 4 0 = 28 := by decide

/-- Every nontrivial irrep has c ≥ 4/3. -/
theorem c3_nontrivial (p q : Nat) (h : p + q ≥ 1) : c3 p q ≥ 4 := by
  unfold c3; cases p <;> cases q <;> simp_all <;> grind

/-- Every irrep other than 1, 3, 3̄ has c ≥ 3. -/
theorem c3_ge_adj (p q : Nat) (h : p + q ≥ 2) : c3 p q ≥ 9 := by
  unfold c3
  rcases p with _ | _ | p <;> rcases q with _ | _ | q <;> simp_all <;> grind

/-! ## Layer 3: finite support check on each graph -/

abbrev Graph := List (Nat × Nat)

def deg (s : Graph) (v : Nat) : Nat := (s.filter (fun e => e.1 == v || e.2 == v)).length

def verts (s : Graph) : List Nat := (s.map (·.1) ++ s.map (·.2)).eraseDups

/-- support has no vertex of degree one (necessary condition from gauge invariance) -/
def admissible (s : Graph) : Bool := (verts s).all (fun v => deg s v != 1)

def reach (s : Graph) : Nat → List Nat → List Nat
  | 0, acc => acc
  | n+1, acc =>
    let nxt := s.foldl (fun a e =>
      if a.contains e.1 && !a.contains e.2 then e.2 :: a
      else if a.contains e.2 && !a.contains e.1 then e.1 :: a else a) acc
    reach s n nxt

def connected (s : Graph) : Bool :=
  match verts s with
  | [] => true
  | v :: _ => (verts s).all (fun w => (reach s (s.length) [v]).contains w)

/-- a single simple cycle of length 4 or 6 -/
def shortCycle (s : Graph) : Bool :=
  (s.length == 4 || s.length == 6) && (verts s).all (fun v => deg s v == 2) && connected s

def choose : Nat → List (Nat × Nat) → List Graph
  | 0, _ => [[]]
  | _+1, [] => []
  | k+1, e :: es => (choose k es).map (e :: ·) ++ choose (k+1) es

def smallSupports (g : Graph) : List Graph :=
  (List.range 6).flatMap (fun k => choose (k+1) g)

/-- The Prop the floor needs: every admissible nonempty support with ≤ 6 links is a short cycle. -/
def SmallSupportsAreCycles (g : Graph) : Prop := ∀ s ∈ smallSupports g, admissible s = true → shortCycle s = true

instance (g : Graph) : Decidable (SmallSupportsAreCycles g) := by unfold SmallSupportsAreCycles; infer_instance

-- vertices of the unit cube as binary 0..7, edges at Hamming distance 1
def cubeE : Graph := [(0,1),(2,3),(4,5),(6,7),(0,2),(1,3),(4,6),(5,7),(0,4),(1,5),(2,6),(3,7)]
-- corner: cube without vertex 7
def cornerE : Graph := cubeE.filter (fun e => e.1 != 7 && e.2 != 7)
-- two squares sharing one link: 0-1-2 / 3-4-5 ladder
def twoE : Graph := [(0,1),(1,2),(3,4),(4,5),(0,3),(1,4),(2,5)]
-- three-square strip: ladder 0..3 / 4..7
def stripE : Graph := [(0,1),(1,2),(2,3),(4,5),(5,6),(6,7),(0,4),(1,5),(2,6),(3,7)]

set_option maxRecDepth 200000 in
theorem two_cycles : SmallSupportsAreCycles twoE := by decide +kernel
set_option maxRecDepth 200000 in
theorem strip_cycles : SmallSupportsAreCycles stripE := by decide +kernel
set_option maxRecDepth 200000 in
theorem corner_cycles : SmallSupportsAreCycles cornerE := by decide +kernel
set_option maxRecDepth 200000 in
theorem cube_cycles : SmallSupportsAreCycles cubeE := by decide +kernel


/-! ### Fused checker (no materialized subset list), for the 20-link double cube -/
def allChoose (f : Graph → Bool) : Nat → Graph → Graph → Bool
  | 0, _, acc => f acc
  | _+1, [], _ => true
  | k+1, e :: es, acc => allChoose f k es (acc ++ [e]) && allChoose f (k+1) es acc

theorem allChoose_eq (f : Graph → Bool) (k : Nat) (l acc : Graph) :
    allChoose f k l acc = (choose k l).all (fun s => f (acc ++ s)) := by
  induction l generalizing k acc with
  | nil => cases k <;> simp [allChoose, choose]
  | cons e es ih =>
    cases k with
    | zero => simp [allChoose, choose]
    | succ k =>
      simp only [allChoose, choose, List.all_append, List.all_map, ih]
      congr 1
      simp [Function.comp_def, List.append_assoc]

def hypB (s : Graph) : Bool := !(admissible s) || shortCycle s

def checkB (g : Graph) : Bool := (List.range 6).all (fun k => allChoose hypB (k+1) g [])

theorem checkB_sound (g : Graph) (h : checkB g = true) : SmallSupportsAreCycles g := by
  intro s hs ha
  simp only [smallSupports, List.mem_flatMap, List.mem_range] at hs
  obtain ⟨k, hk, hs⟩ := hs
  have := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  rw [allChoose_eq] at this
  have h2 := List.all_eq_true.mp this s hs
  simp [hypB, ha] at h2
  exact h2

-- two cubes sharing a face (2x1x1 box), 12 vertices, 20 links
def dcubeE : Graph := [(0,4),(0,2),(0,1),(1,5),(1,3),(2,6),(2,3),(3,7),(4,8),(4,6),(4,5),(5,9),(5,7),(6,10),(6,7),(7,11),(8,10),(8,9),(9,11),(10,11)]

-- NOT YET CHECKED: `checkB dcubeE = true` runs out of memory in the kernel here.
-- Once it is checked, `checkB_sound` gives `SmallSupportsAreCycles dcubeE`.

theorem edge_counts : twoE.length = 7 ∧ stripE.length = 10 ∧ cornerE.length = 9 ∧ cubeE.length = 12 := by decide

/-! ## Combining (energies scaled by 3) -/

/-- Not a short cycle and admissible ⇒ ≥ 7 nontrivial links ⇒ 3C ≥ 28. -/
theorem long_support_floor (n : Nat) (cs : List Nat) (hlen : cs.length = n) (hn : n ≥ 7)
    (hc : ∀ x ∈ cs, x ≥ 4) : cs.sum ≥ 28 := by
  induction cs generalizing n with
  | nil => simp at hlen; omega
  | cons x xs ih =>
    simp at hlen
    have hx := hc x (by simp)
    by_cases h7 : xs.length ≥ 7
    · have := ih xs.length rfl h7 (fun y hy => hc y (by simp [hy])); simp; omega
    · have hall : ∀ y ∈ xs, y ≥ 4 := fun y hy => hc y (by simp [hy])
      have : xs.sum ≥ 4 * xs.length := by
        clear ih h7 hlen hc hx
        induction xs with
        | nil => simp
        | cons y ys ih2 => simp; have := hall y (by simp); have := ih2 (fun z hz => hall z (by simp [hz])); omega
      simp; omega

/-- A short cycle carrying one irrep: energy len·c; if 3C > 24 then 3C ≥ 28. -/
theorem cycle_floor (len p q : Nat) (hl : len = 4 ∨ len = 6) (hgt : len * c3 p q > 24) :
    len * c3 p q ≥ 28 := by
  by_cases h : p + q ≥ 2
  · have := c3_ge_adj p q h; rcases hl with rfl | rfl <;> omega
  · have : (p = 0 ∧ q = 0) ∨ (p = 1 ∧ q = 0) ∨ (p = 0 ∧ q = 1) := by omega
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hl with rfl | rfl <;> simp [c3] at hgt ⊢


/-! ## Non-vacuity and false control -/
-- admissible small supports really occur: cube has 6 four-cycles and 16 six-cycles
theorem cube_count : ((smallSupports cubeE).filter admissible).length = 22 := by decide +kernel
-- K_{2,3} (theta graph 2,2,2): an admissible 6-link support that is not a cycle, so the hypothesis FAILS
def k23E : Graph := [(0,2),(2,1),(0,3),(3,1),(0,4),(4,1)]
theorem k23_control : ¬ SmallSupportsAreCycles k23E := by decide +kernel

end TailFloor
