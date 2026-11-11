import ThetaFloorTriality

/- False control: the ThetaFloor table row `((0,0), (0,1), (1,0))` (`1, 3̄, 3`, in `thetaList`)
   with the triality of its `3̄` arm swapped `p ↔ q`, i.e. the arm given the triality of
   `(1,0)`, which is 1, instead of `triality (0,1) = 2`. The total triality is then
   `0 + 1 + 1 = 2`, so the row would violate the centre-character condition proved for
   `V(p, q)` arms (`swap_entry_rejected` proves the negation). Must fail to compile. -/
namespace ThetaFloorTriality

open ThetaFloor ThetaTriality TrialityVertex

theorem theta_entry_swapped_triality :
    ((0, 0), (0, 1), (1, 0)) ∈ thetaList ∧
      vertexTri [(true, (0, 0)), (true, conj (0, 1)), (true, (1, 0))] = 0 := by decide

end ThetaFloorTriality
