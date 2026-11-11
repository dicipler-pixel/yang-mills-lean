import TailFloor
/-! Kernel check of the double-cube support hypothesis. Not in the default build:
it exhausted memory locally. Run with `lake env lean TailFloorDoubleCube.lean`. -/
namespace TailFloor
set_option maxRecDepth 400000 in
theorem dcube_checkB : checkB dcubeE = true := by decide +kernel
theorem dcube_cycles : SmallSupportsAreCycles dcubeE := checkB_sound _ dcube_checkB
end TailFloor
