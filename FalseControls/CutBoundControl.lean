import CutBound

/- False control: claims the cut bound is 5 per cut, but the fundamental 3 costs
   exactly 4, so two cuts of 3 cost 8 < 10. Must fail to compile. -/
namespace CutBound

theorem cut_bound_too_strong :
    5 * 2 ≤ ((List.replicate 2 ((1, 0) : ThetaFloor.Irrep)).map ThetaFloor.cas3).sum := by decide

end CutBound
