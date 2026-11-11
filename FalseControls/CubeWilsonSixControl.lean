import CubeWilsonSix
open CategoryTheory TailFloor GaugeSupport NtListSupport PermCube
open scoped Classical

/- False control: the sign 6-cycle labelling of `S₃` (boundary of two adjacent cube faces)
   has exactly 4 non-trivial links. It has 6: `cube_six_card_S3`, and rewriting with it
   leaves the false goal `6 = 4`. -/
example : (Finset.univ.filter (NTe (simpleIrr ∘ face6π signChar))).card = 4 := by
  rw [cube_six_card_S3]
