import GraphInstances

/- False control: claims the double cube has a 5-link support that is a single short cycle,
   as a gauge-invariant component with exactly 5 non-trivial links would need
   (`GraphInstances.dcube_gauge_support_card` forces 4 or 6). The witness is a genuine 5-link
   sublist of `dcubeE`, but a short cycle has 4 or 6 links. Must fail to compile. -/
namespace GraphInstances

theorem dcube_five_link_cycle :
    dcubeFive.Sublist TailFloor.dcubeE ∧ TailFloor.shortCycle dcubeFive = true := by
  decide

end GraphInstances
