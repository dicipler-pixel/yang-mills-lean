import SupportDichotomy

/- False control: claims the strip has a 3-link support that the short-cycle case accepts.
   The witness is a genuine 3-link sublist of `stripE` (the path 0-1-2-3), but a short cycle
   has 4 or 6 links and no vertex of degree one. Must fail to compile. -/
namespace SupportDichotomy

theorem strip_three_link_cycle :
    stripThree.Sublist TailFloor.stripE ∧ TailFloor.shortCycle stripThree = true := by
  decide

end SupportDichotomy
