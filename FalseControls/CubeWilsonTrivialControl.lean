import CubeWilsonExistence
open CategoryTheory TailFloor GaugeSupport NtListSupport PermCube
open scoped Classical

/- False control: the face Wilson loop labelling built from the trivial character of `S₃`
   has exactly 4 non-trivial links. With `φ = 1` every link label is the trivial ideal, so
   there are none: the negation is proved as `cube_wilson_trivial_card_S3` (card = 0), and
   rewriting with it leaves the false goal `0 = 4`. -/
example : (Finset.univ.filter (NTe (simpleIrr ∘ faceπ (1 : S3 →* ℂˣ)))).card = 4 := by
  rw [cube_wilson_trivial_card_S3]
