import TrialityVertex

/- False control (n = 3): claims `3 ⊗ 3 ⊗ 1` is conserved (total triality 2). Must fail to
   compile. -/
namespace TrialityVertex

theorem three_three_one_conserved : vertexTri [(true, (1, 0)), (true, (1, 0)), (true, (0, 0))] = 0 := by
  decide

end TrialityVertex
