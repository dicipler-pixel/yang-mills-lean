import TrialityVertex

/- False control (n = 4): claims four outgoing `3`s are conserved (total triality 4 ≡ 1).
   Must fail to compile. -/
namespace TrialityVertex

theorem four_fund_conserved :
    vertexTri [(true, (1, 0)), (true, (1, 0)), (true, (1, 0)), (true, (1, 0))] = 0 := by
  decide

end TrialityVertex
