import TrialityVertex

/- False control (n = 2): claims `3` out and `3̄` in is conserved. The incoming `3̄` enters
   as its conjugate `3`, so the total triality is 1 + 1 = 2 ≠ 0. Must fail to compile. -/
namespace TrialityVertex

theorem two_valent_mismatch_conserved : vertexTri [(true, (1, 0)), (false, (0, 1))] = 0 := by
  decide

end TrialityVertex
