import CutFlux

/- False control: claims the ring cut bound is 5 per link. A ring of fundamentals
   (triality 1 on every link, so Gauss's law holds) costs exactly 4 per link,
   so two links cost 8 < 10. Must fail to compile. -/
namespace CutFlux

theorem ring_cut_bound_too_strong :
    5 * 2 ≤ ((List.finRange 2).map (fun _ => ThetaFloor.cas3 ((1, 0) : ThetaFloor.Irrep))).sum := by
  decide

end CutFlux
