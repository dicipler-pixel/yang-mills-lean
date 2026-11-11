import NtListSupport

/- False control: a square with a pendant link (vertex 4 has degree one) claimed admissible,
   i.e. claimed to be the support of a labelling with a nonzero invariant at every vertex.
   The vertex rule forbids a vertex with exactly one non-trivial link. Must fail to compile. -/
namespace NtListSupport

theorem dangling_support_admissible :
    TailFloor.admissible [(0, 1), (1, 2), (2, 3), (3, 0), (0, 4)] = true := by decide

end NtListSupport
