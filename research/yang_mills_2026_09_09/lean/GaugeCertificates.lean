import Mathlib

/- Closed rational matrix certificates for the actual shared-link SU(3) model.
   The kernel checks each displayed factorization, diagonal and sign claim.
   These statements do NOT formalize the Haar integral, Hilbert-space basis
   completeness, the analytic tail, or Sylvester inertia. Those links have
   separately supplied written proofs and exact Python checks. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace YangMillsSeptember9

def innerK : Matrix (Fin 10) (Fin 10) ℚ :=
  !![(12/7), (-20/21), (-20/21), 0, 0, 0, 0, 0, 0, 0;
     (-20/21), (64/21), (-20/21), (-20/21), (-20/21), 0, 0, 0, 0, 0;
     (-20/21), (-20/21), (64/21), 0, (-20/21), (-20/21), 0, 0, 0, 0;
     0, (-20/21), 0, (106/21), (-20/21), 0, (-20/21), (-20/21), 0, 0;
     0, (-20/21), (-20/21), (-20/21), (33/7), (-20/21), 0, (-20/21), (-20/21), 0;
     0, 0, (-20/21), 0, (-20/21), (106/21), 0, 0, (-20/21), (-20/21);
     0, 0, 0, (-20/21), 0, 0, (3202/441), (-520/441), 0, 0;
     0, 0, 0, (-20/21), (-20/21), 0, (-520/441), (2908/441), (-520/441), 0;
     0, 0, 0, 0, (-20/21), (-20/21), 0, (-520/441), (2908/441), (-520/441);
     0, 0, 0, 0, 0, (-20/21), 0, 0, (-520/441), (3202/441)]

def innerL : Matrix (Fin 10) (Fin 10) ℚ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     (-5/9), 1, 0, 0, 0, 0, 0, 0, 0, 0;
     (-5/9), (-10/17), 1, 0, 0, 0, 0, 0, 0, 0;
     0, (-45/119), (-50/147), 1, 0, 0, 0, 0, 0, 0;
     0, (-45/119), (-45/49), (-2820/6941), 1, 0, 0, 0, 0, 0;
     0, 0, (-85/147), (-500/6941), (-1998440/2267913), 1, 0, 0, 0, 0;
     0, 0, 0, (-1470/6941), (-131600/755971), (-9753000/65430839), 1, 0, 0, 0;
     0, 0, 0, (-1470/6941), (-1366540/2267913), (-29737400/65430839), (-1997796880/7691704303), 1, 0, 0;
     0, 0, 0, 0, (-971740/2267913), (-42663530/65430839), (-6244854000/99992155939), (-2272397086090/3858688843131), 1, 0;
     0, 0, 0, 0, 0, (-22679130/65430839), (-2048130000/99992155939), (-132774593000/1286229614377), (-11534406893776440/18873999327083231), 1]

def innerD : Fin 10 → ℚ := ![(12/7), (68/27), (28/17), (13882/3087), (755971/340109), (130861678/47626173), (199984311878/28854999999), (5144918457508/1130680532541), (75495997308332924/22121863137670023), (46650308156624597462/8323433703243704871)]

def outerK : Matrix (Fin 7) (Fin 7) ℚ :=
  !![-4, (-1/2), (-1/2), (-1/2), (-1/2), 0, 0;
     (-1/2), (337/384), (-79/128), (-15/128), (-5/48), (-79/384), (-5/128);
     (-1/2), (-79/128), (337/384), (-5/48), (-15/128), (-5/128), (-79/384);
     (-1/2), (-15/128), (-5/48), (337/384), (-79/128), (-5/128), (-79/384);
     (-1/2), (-5/48), (-15/128), (-79/128), (337/384), (-79/384), (-5/128);
     0, (-79/384), (-5/128), (-5/128), (-79/384), (683/192), (-5/64);
     0, (-5/128), (-79/384), (-79/384), (-5/128), (-5/64), (683/192)]

def outerL : Matrix (Fin 7) (Fin 7) ℚ :=
  !![1, 0, 0, 0, 0, 0, 0;
     (1/8), 1, 0, 0, 0, 0, 0;
     (1/8), (-213/361), 1, 0, 0, 0, 0;
     (1/8), (-21/361), (-277/2296), 1, 0, 0, 0;
     (1/8), (-16/361), (-297/2296), (-166539/272729), 1, 0, 0;
     0, (-79/361), (-11121/42476), (-20686/272729), (-10255/21423), 1, 0;
     0, (-15/361), (-15857/42476), (-207722/818187), (-2629/7141), (-1098243/13703459), 1]

def outerD : Fin 7 → ℚ := ![-4, (361/384), (10619/17328), (272729/293888), (20316145/34909312), (13703459/4113216), (408246943/123331131)]

theorem inner_factorization :
    innerK = (innerL * Matrix.diagonal innerD) * innerL.transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [innerK, innerL, innerD, Matrix.mul_apply, Matrix.diagonal_apply,
      Matrix.transpose_apply, Matrix.vecMul_diagonal, Matrix.cons_val_two, Fin.sum_univ_succ]

theorem inner_unit_diagonal : ∀ i : Fin 10, innerL i i = 1 := by
  intro i; fin_cases i <;> norm_num [innerL]

theorem inner_lower_triangular :
    ∀ i j : Fin 10, i < j → innerL i j = 0 := by
  intro i j; fin_cases i <;> fin_cases j <;> norm_num [innerL]

theorem inner_pivots_positive : ∀ i : Fin 10, 0 < innerD i := by
  intro i; fin_cases i <;> norm_num [innerD]

theorem outer_factorization :
    outerK = (outerL * Matrix.diagonal outerD) * outerL.transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [outerK, outerL, outerD, Matrix.mul_apply, Matrix.diagonal_apply,
      Matrix.transpose_apply, Matrix.vecMul_diagonal, Matrix.cons_val_two, Fin.sum_univ_succ]

theorem outer_unit_diagonal : ∀ i : Fin 7, outerL i i = 1 := by
  intro i; fin_cases i <;> norm_num [outerL]

theorem outer_lower_triangular :
    ∀ i j : Fin 7, i < j → outerL i j = 0 := by
  intro i j; fin_cases i <;> fin_cases j <;> norm_num [outerL]

theorem outer_first_negative : outerD 0 < 0 := by norm_num [outerD]

theorem outer_other_pivots_positive :
    ∀ i : Fin 6, 0 < outerD i.succ := by
  intro i; fin_cases i <;> norm_num [outerD, Matrix.cons_val_two]

theorem allocated_local_casimir :
    (7/2 : ℚ) * (1 - 17/20) = 21/40 := by norm_num

theorem inner_normalized_coupling : (1 : ℚ) / (21/40) = 40/21 := by norm_num

theorem inner_normalized_energy : (21/10 : ℚ) / (21/40) = 4 := by norm_num

theorem inner_tail_separation : (4 : ℚ) < 8 := by norm_num

theorem derived_hidden_floor :
    (17/20 : ℚ) * (28/3) + 2*(21/10) = 182/15 := by norm_num

theorem test_energy_separation : (6 : ℚ) < 10 ∧ (10 : ℚ) < 182/15 := by norm_num

theorem outer_tail_denominator : (182/15 : ℚ) - 10 = 32/15 := by norm_num

theorem certified_margin_arithmetic : (10 : ℚ) - 6 = 4 := by norm_num

theorem global_shift_does_not_fix_denominator (d r c : ℚ) :
    (d-c)-(r-c)=d-r := by ring

theorem shared_rectangle_electric : (6 : ℚ)*(4/3)=8 := by norm_num

theorem independent_rectangle_is_wrong : (8 : ℚ)*(4/3) ≠ 8 := by norm_num

theorem first_baryonic_tail : (7 : ℚ)*(4/3)=28/3 := by norm_num

#print axioms inner_factorization
#print axioms inner_unit_diagonal
#print axioms inner_lower_triangular
#print axioms inner_pivots_positive
#print axioms outer_factorization
#print axioms outer_unit_diagonal
#print axioms outer_lower_triangular
#print axioms outer_first_negative
#print axioms outer_other_pivots_positive
#print axioms allocated_local_casimir
#print axioms inner_normalized_coupling
#print axioms inner_normalized_energy
#print axioms inner_tail_separation
#print axioms derived_hidden_floor
#print axioms test_energy_separation
#print axioms outer_tail_denominator
#print axioms certified_margin_arithmetic
#print axioms global_shift_does_not_fix_denominator
#print axioms shared_rectangle_electric
#print axioms independent_rectangle_is_wrong
#print axioms first_baryonic_tail
end YangMillsSeptember9
