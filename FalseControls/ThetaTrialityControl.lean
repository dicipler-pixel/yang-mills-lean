import ThetaTriality

/- False control: claims a singlet with nonzero total triality (3 ⊗ 3 ⊗ 1 has total
   triality 2, so no singlet). Must fail to compile. -/
namespace ThetaTriality

theorem singlet_with_triality :
    ThetaFloor.hasSinglet (1, 0) (1, 0) (0, 0) = true ∧
    (triality (1, 0) + triality (1, 0) + triality (0, 0)) % 3 ≠ 0 := by decide

end ThetaTriality
