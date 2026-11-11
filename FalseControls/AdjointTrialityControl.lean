import CentreCharacterSU3

/- False control: claims the adjoint `8`, as any subrepresentation of `3 ⊗ 3̄`, has triality 1,
   so that `ω·I` acts on it by `ω ^ 1`. Its label is `(1, 1)`, with triality
   `(1 + 2) % 3 = 0`, and the centre acts trivially (`adjoint_centre_trivial`). Must fail to
   compile. -/
namespace CentreCharacterSU3

open ThetaTriality TrialityVertex

theorem adjoint_triality_one {X : FDRep ℂ SU3} (f : X ⟶ tensorRep 1 1)
    [CategoryTheory.Mono f] :
    triality (1, 1) = 1 ∧ CentreActs zω (ω ^ triality (1, 1)) X :=
  ⟨by decide, centreCharacter_of_mono f⟩

end CentreCharacterSU3
