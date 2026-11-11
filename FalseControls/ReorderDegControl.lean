import PermCube

/- False control: claims that reversing the order of a 4-cycle's links changes the degree of
   vertex 1. Degree counts incident links, so it is the same (`PermCube.deg_perm`). Must fail
   to compile. -/
namespace PermCube

theorem reorder_changes_deg :
    TailFloor.deg [(0, 1), (1, 2), (2, 3), (3, 0)] 1 ≠ TailFloor.deg [(3, 0), (2, 3), (1, 2), (0, 1)] 1 := by
  decide

end PermCube
