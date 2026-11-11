import CubeFiniteUnconditional
open CategoryTheory TailFloor GaugeSupport NtListSupport PermCube
open scoped Classical

/- False control: under `S₃` on the cube, a nonzero gauge-invariant Fourier component with
   exactly 3 non-trivial links. The constant state is gauge invariant, but no labelling with
   3 non-trivial links has a nonzero component: `cube_gauge_support_card_S3` forces 4 or 6,
   and the negation is proved as `cube_no_three_links_S3`. The labelling goal stays open. -/
example : ∃ ψ : (Fin 12 → S3) → ℂ, (∀ g, latticeGauge cubeΓ g ψ = ψ) ∧
    ∃ π : Fin 12 → SimpleIdeal S3, fourierProj simpleIrr π ψ ≠ 0 ∧
      (Finset.univ.filter (NTe (simpleIrr ∘ π))).card = 3 := by
  refine ⟨fun _ => 1, fun g => ?_, ?_⟩
  · funext U
    rw [latticeGauge_apply]
