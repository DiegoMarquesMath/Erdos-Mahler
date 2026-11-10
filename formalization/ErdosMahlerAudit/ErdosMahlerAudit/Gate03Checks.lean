module

public import ErdosMahlerAudit.Gate03.Successors

/-! Reproducible Gate 03 statement, definition, and foundational-axiom audit. -/

set_option format.width 110
set_option pp.universes true
set_option pp.fullNames true

-- Exact existing objects and the library bridge; no replacement denominator set.
#check @Real.convergent
#print Real.convergent
#check @Real.convergent_zero
#check @Real.convergent_succ
#check @Real.convs_eq_convergent
#print axioms Real.convs_eq_convergent
#print ErdosMahlerAudit.alpha
#check @ErdosMahlerAudit.alpha_irrational
#print ErdosMahlerAudit.convergentDenominators
#print ErdosMahlerAudit.Gate02.candidateIndices
#print ErdosMahlerAudit.Gate02.rho
#check @ErdosMahlerAudit.Phi_R
#check @ErdosMahlerAudit.Gate02.Phi_image_J
#check @ErdosMahlerAudit.Gate02.conditional_successors

-- Pinned-library dependencies whose precise types matter to the argument.
#check @GenContFract.of_convergence_epsilon
#print axioms GenContFract.of_convergence_epsilon
#check @GenContFract.of_correctness_of_terminatedAt
#print axioms GenContFract.of_correctness_of_terminatedAt
#check @GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq
#print axioms GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq
#check @GenContFract.contsAux_recurrence
#print axioms GenContFract.contsAux_recurrence
#check @GenContFract.succ_nth_fib_le_of_nth_den
#print axioms GenContFract.succ_nth_fib_le_of_nth_den
#check @GenContFract.of_den_mono
#print axioms GenContFract.of_den_mono
#check @GenContFract.abs_sub_convs_le
#print axioms GenContFract.abs_sub_convs_le
#check @Rat.pos
#print axioms Rat.pos
#check @Rat.reduced
#print axioms Rat.reduced
#check @Rat.den_dvd
#print axioms Rat.den_dvd
#check @Rat.cast_divInt
#print axioms Rat.cast_divInt
#check @Nat.dvd_factorial
#print axioms Nat.dvd_factorial
#check @Int.dvd_of_dvd_mul_right_of_gcd_one
#print axioms Int.dvd_of_dvd_mul_right_of_gcd_one
#check @Int.eq_zero_of_abs_lt_dvd
#print axioms Int.eq_zero_of_abs_lt_dvd
#check @Int.card_Icc_of_le
#print axioms Int.card_Icc_of_le
#check @Finset.card_le_card_of_injOn
#print axioms Finset.card_le_card_of_injOn
#check @Int.fract_nonneg
#print axioms Int.fract_nonneg
#check @Int.fract_lt_one
#print axioms Int.fract_lt_one

-- Approximation.lean
#check @ErdosMahlerAudit.Gate03.alpha_not_terminated
#print axioms ErdosMahlerAudit.Gate03.alpha_not_terminated
#check @ErdosMahlerAudit.Gate03.continuants_integral
#print axioms ErdosMahlerAudit.Gate03.continuants_integral
#check @ErdosMahlerAudit.Gate03.continuant_den_pos
#print axioms ErdosMahlerAudit.Gate03.continuant_den_pos
#check @ErdosMahlerAudit.Gate03.convergent_den_le_continuant
#print axioms ErdosMahlerAudit.Gate03.convergent_den_le_continuant
#check @ErdosMahlerAudit.Gate03.convergent_error_le
#print axioms ErdosMahlerAudit.Gate03.convergent_error_le
#check @ErdosMahlerAudit.Gate03.convergent_error_lt
#print axioms ErdosMahlerAudit.Gate03.convergent_error_lt
#check @ErdosMahlerAudit.Gate03.convergentDenominators_approximation
#print axioms ErdosMahlerAudit.Gate03.convergentDenominators_approximation
#check @ErdosMahlerAudit.Gate03.translated_grid_error
#print axioms ErdosMahlerAudit.Gate03.translated_grid_error

-- Denominators.lean
#check @ErdosMahlerAudit.Gate03.irrational_integer_gap
#print axioms ErdosMahlerAudit.Gate03.irrational_integer_gap
#check @ErdosMahlerAudit.Gate03.irrational_bounded_denominator_gap
#print axioms ErdosMahlerAudit.Gate03.irrational_bounded_denominator_gap
#check @ErdosMahlerAudit.Gate03.convergent_alpha_epsilon
#print axioms ErdosMahlerAudit.Gate03.convergent_alpha_epsilon
#check @ErdosMahlerAudit.Gate03.convergent_denominators_eventually_gt
#print axioms ErdosMahlerAudit.Gate03.convergent_denominators_eventually_gt
#check @ErdosMahlerAudit.Gate03.convergentDenominators_pos
#print axioms ErdosMahlerAudit.Gate03.convergentDenominators_pos
#check @ErdosMahlerAudit.Gate03.convergentDenominators_unbounded
#print axioms ErdosMahlerAudit.Gate03.convergentDenominators_unbounded
#check @ErdosMahlerAudit.Gate03.one_mem_convergentDenominators
#print axioms ErdosMahlerAudit.Gate03.one_mem_convergentDenominators

-- Rotation.lean
#check @ErdosMahlerAudit.Gate03.card_le_of_integer_lifts
#print axioms ErdosMahlerAudit.Gate03.card_le_of_integer_lifts
#check @ErdosMahlerAudit.Gate03.grid_lift_injective
#print axioms ErdosMahlerAudit.Gate03.grid_lift_injective
#check @ErdosMahlerAudit.Gate03.rotation_closed_upper
#print axioms ErdosMahlerAudit.Gate03.rotation_closed_upper
#check @ErdosMahlerAudit.Gate03.openRotationIndices
#print axioms ErdosMahlerAudit.Gate03.openRotationIndices
#check @ErdosMahlerAudit.Gate03.rotation_open_discrepancy
#print axioms ErdosMahlerAudit.Gate03.rotation_open_discrepancy
#check @ErdosMahlerAudit.Gate03.Phi_injOn_positive
#print axioms ErdosMahlerAudit.Gate03.Phi_injOn_positive
#check @ErdosMahlerAudit.Gate03.Phi_J_endpoints
#print axioms ErdosMahlerAudit.Gate03.Phi_J_endpoints
#check @ErdosMahlerAudit.Gate03.candidateIndices_eq_openRotationIndices
#print axioms ErdosMahlerAudit.Gate03.candidateIndices_eq_openRotationIndices
#check @ErdosMahlerAudit.Gate03.candidate_discrepancy
#print axioms ErdosMahlerAudit.Gate03.candidate_discrepancy
#check @ErdosMahlerAudit.Gate03.rotation_uniform
#print axioms ErdosMahlerAudit.Gate03.rotation_uniform

-- Successors.lean
#check @ErdosMahlerAudit.Gate03.counting_implies_admissible_choices
#print axioms ErdosMahlerAudit.Gate03.counting_implies_admissible_choices
#check @ErdosMahlerAudit.Gate03.counting_implies_successors
#print axioms ErdosMahlerAudit.Gate03.counting_implies_successors

#print ErdosMahlerAudit.Gate03.openRotationIndices
#print ErdosMahlerAudit.Gate03.convergentDenominators_unbounded
#print ErdosMahlerAudit.Gate03.rotation_uniform
#print ErdosMahlerAudit.Gate03.counting_implies_successors

-- Central types with implicit arguments displayed, as an additional audit.
set_option pp.explicit true in
#check @ErdosMahlerAudit.Gate03.convergentDenominators_unbounded
set_option pp.explicit true in
#check @ErdosMahlerAudit.Gate03.rotation_uniform
set_option pp.explicit true in
#check @ErdosMahlerAudit.Gate03.counting_implies_successors

-- Boundary instantiations: the original counting hypothesis remains visible.
#check ErdosMahlerAudit.Gate03.counting_implies_successors (4 : ℝ) (by norm_num)
#check ErdosMahlerAudit.Gate03.rotation_open_discrepancy
  ErdosMahlerAudit.Gate03.one_mem_convergentDenominators 0 1
  (by norm_num) (by norm_num) (by norm_num)
