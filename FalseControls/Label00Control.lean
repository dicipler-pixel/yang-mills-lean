import HntLabels

/- False control: claims a link labelled `(0, 0)` is non-trivial. `V(0, 0) ≅ 𝟙`
   (`irrep00Iso`), so it is trivial; through `NTe_irrPQ_iff` the claim reduces to
   `(0, 0) ≠ (0, 0)`, which `decide` refutes. Must fail to compile. -/
namespace HntLabels

theorem label00_nontrivial :
    NtListSupport.NTe (irrPQ ∘ fun _ : Unit => ((0 : ℕ), (0 : ℕ))) () :=
  (NTe_irrPQ_iff _ ()).2 (by decide)

end HntLabels
