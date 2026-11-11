import ThetaFloor

/- False control: these claims are deliberately false and must fail to compile.
   (1) a fifth realization of level 40/3: octet ⊗ octet ⊗ trivial (its level is 12, i.e. 3·level = 36);
   (2) level 13 (3·level = 39) occurs among the admissible labellings. -/
namespace ThetaFloor

theorem fifth_40_3 :
    admissible (1, 1) (1, 1) (0, 0) = true ∧ level3 (1, 1) (1, 1) (0, 0) = 40 := by decide

theorem level_13_occurs : 39 ∈ levelSet3 := by decide

end ThetaFloor
