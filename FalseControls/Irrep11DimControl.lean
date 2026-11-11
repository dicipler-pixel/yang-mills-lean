import IrrepIrreducibleSU3

/- False control: claims that `V(1, 1)`, the SU(3)-span of `e₁ ⊗ e₃* ⊗ 1` inside `3 ⊗ 3̄ ⊗ 𝟙`,
   is 9-dimensional, i.e. the whole of `3 ⊗ 3̄`. The proof attempt rewrites with the proved
   dimension `finrank_irrepRep11` and is left with `8 = 9`; Lean rejects it with unsolved goals.
   The claim is false: `V(1, 1)` is the kernel of the contraction `3 ⊗ 3̄ → ℂ`, the traceless
   part, of dimension 8 (`irrepSub11_eq_ker_contract`, `irrep11_finrank_ne_nine`); the trace
   singlet is the missing ninth direction. Must fail to compile. -/
namespace IrrepIrreducibleSU3

open CentreCharacterSU3 IrrepEmbedSU3

theorem irrep11_finrank_nine : Module.finrank ℂ (irrepRep 1 1) = 9 := by
  rw [finrank_irrepRep11]

end IrrepIrreducibleSU3
