import NtListSupport

/- False control: `K_{2,3}` claimed to be a single 4- or 6-cycle. It is admissible but its
   two hubs have degree three. Must fail to compile. -/
namespace NtListSupport

theorem k23_is_short_cycle : TailFloor.shortCycle TailFloor.k23E = true := by decide

end NtListSupport
