module

public import ErdosMahlerAudit.Gate02.AdmissibleChoices

/-! Gate 02 reproducible declaration inventory and axiom audit. -/

set_option format.width 110
set_option pp.universes true
set_option pp.fullNames true

-- Actual existing Gate 01 declarations; no guessed or replacement names.
#check @ErdosMahlerAudit.alpha
#print axioms ErdosMahlerAudit.alpha
#print ErdosMahlerAudit.alpha
#check @ErdosMahlerAudit.a
#print axioms ErdosMahlerAudit.a
#print ErdosMahlerAudit.a
#check @ErdosMahlerAudit.R
#print axioms ErdosMahlerAudit.R
#print ErdosMahlerAudit.R
#check @ErdosMahlerAudit.Phi
#print axioms ErdosMahlerAudit.Phi
#print ErdosMahlerAudit.Phi
#check @ErdosMahlerAudit.convergentDenominators
#print axioms ErdosMahlerAudit.convergentDenominators
#print ErdosMahlerAudit.convergentDenominators
#check @ErdosMahlerAudit.Exceptional
#print axioms ErdosMahlerAudit.Exceptional
#print ErdosMahlerAudit.Exceptional
#check @ErdosMahlerAudit.exceptionalCount
#print axioms ErdosMahlerAudit.exceptionalCount
#print ErdosMahlerAudit.exceptionalCount
#check @ErdosMahlerAudit.a_cast_eq_ceil
#print axioms ErdosMahlerAudit.a_cast_eq_ceil
#check @ErdosMahlerAudit.R_num
#print axioms ErdosMahlerAudit.R_num
#check @ErdosMahlerAudit.R_den
#print axioms ErdosMahlerAudit.R_den
#check @ErdosMahlerAudit.R_coprime
#print axioms ErdosMahlerAudit.R_coprime
#check @ErdosMahlerAudit.R_mem_Ioo
#print axioms ErdosMahlerAudit.R_mem_Ioo
#check @ErdosMahlerAudit.Phi_R
#print axioms ErdosMahlerAudit.Phi_R
#check @ErdosMahlerAudit.exceptional_den_bound
#print axioms ErdosMahlerAudit.exceptional_den_bound
#check @Rat.num
#check @Rat.den
#check @Rat.pos
#check @Rat.reduced
#check @Rat.num_div_den
#check @Set.Ioo

-- ErdosMahlerAudit/Gate02/Exceptional.lean
#check @ErdosMahlerAudit.Gate02.badIndices
#print axioms ErdosMahlerAudit.Gate02.badIndices
#print ErdosMahlerAudit.Gate02.badIndices
#check @ErdosMahlerAudit.Gate02.E
#print axioms ErdosMahlerAudit.Gate02.E
#print ErdosMahlerAudit.Gate02.E
#check @ErdosMahlerAudit.Gate02.E_eq_exceptionalCount
#print axioms ErdosMahlerAudit.Gate02.E_eq_exceptionalCount
#check @ErdosMahlerAudit.Gate02.mem_badIndices
#print axioms ErdosMahlerAudit.Gate02.mem_badIndices
#check @ErdosMahlerAudit.Gate02.exceptional_canonical
#print axioms ErdosMahlerAudit.Gate02.exceptional_canonical

-- ErdosMahlerAudit/Gate02/FiniteCounting.lean
#check @ErdosMahlerAudit.Gate02.radius
#print axioms ErdosMahlerAudit.Gate02.radius
#print ErdosMahlerAudit.Gate02.radius
#check @ErdosMahlerAudit.Gate02.J
#print axioms ErdosMahlerAudit.Gate02.J
#print ErdosMahlerAudit.Gate02.J
#check @ErdosMahlerAudit.Gate02.nu
#print axioms ErdosMahlerAudit.Gate02.nu
#print ErdosMahlerAudit.Gate02.nu
#check @ErdosMahlerAudit.Gate02.cutoff
#print axioms ErdosMahlerAudit.Gate02.cutoff
#print ErdosMahlerAudit.Gate02.cutoff
#check @ErdosMahlerAudit.Gate02.rho
#print axioms ErdosMahlerAudit.Gate02.rho
#print ErdosMahlerAudit.Gate02.rho
#check @ErdosMahlerAudit.Gate02.candidateIndices
#print axioms ErdosMahlerAudit.Gate02.candidateIndices
#print ErdosMahlerAudit.Gate02.candidateIndices
#check @ErdosMahlerAudit.Gate02.admissibleIndices
#print axioms ErdosMahlerAudit.Gate02.admissibleIndices
#print ErdosMahlerAudit.Gate02.admissibleIndices
#check @ErdosMahlerAudit.Gate02.radius_pos
#print axioms ErdosMahlerAudit.Gate02.radius_pos
#check @ErdosMahlerAudit.Gate02.radius_eq_Q
#print axioms ErdosMahlerAudit.Gate02.radius_eq_Q
#check @ErdosMahlerAudit.Gate02.cutoff_pos
#print axioms ErdosMahlerAudit.Gate02.cutoff_pos
#check @ErdosMahlerAudit.Gate02.parent_parameters
#print axioms ErdosMahlerAudit.Gate02.parent_parameters
#check @ErdosMahlerAudit.Gate02.mem_candidateIndices
#print axioms ErdosMahlerAudit.Gate02.mem_candidateIndices
#check @ErdosMahlerAudit.Gate02.mem_admissibleIndices
#print axioms ErdosMahlerAudit.Gate02.mem_admissibleIndices
#check @ErdosMahlerAudit.Gate02.admissible_card_lower
#print axioms ErdosMahlerAudit.Gate02.admissible_card_lower
#check @ErdosMahlerAudit.Gate02.candidate_card_le
#print axioms ErdosMahlerAudit.Gate02.candidate_card_le
#check @ErdosMahlerAudit.Gate02.admissible_card_lower_real
#print axioms ErdosMahlerAudit.Gate02.admissible_card_lower_real
#check @ErdosMahlerAudit.Gate02.admissible_index_positive
#print axioms ErdosMahlerAudit.Gate02.admissible_index_positive
#check @ErdosMahlerAudit.Gate02.admissible_approximation_lower
#print axioms ErdosMahlerAudit.Gate02.admissible_approximation_lower

-- ErdosMahlerAudit/Gate02/Density.lean
#check @ErdosMahlerAudit.Gate02.Phi_image_J
#print axioms ErdosMahlerAudit.Gate02.Phi_image_J
#check @ErdosMahlerAudit.Gate02.rho_pos
#print axioms ErdosMahlerAudit.Gate02.rho_pos
#check @ErdosMahlerAudit.Gate02.R_le_two_sub_inv
#print axioms ErdosMahlerAudit.Gate02.R_le_two_sub_inv
#check @ErdosMahlerAudit.Gate02.three_le_Q
#print axioms ErdosMahlerAudit.Gate02.three_le_Q
#check @ErdosMahlerAudit.Gate02.interval_upper
#print axioms ErdosMahlerAudit.Gate02.interval_upper
#check @ErdosMahlerAudit.Gate02.J_subset_Ioo
#print axioms ErdosMahlerAudit.Gate02.J_subset_Ioo
#check @ErdosMahlerAudit.Gate02.cutoff_ge_two
#print axioms ErdosMahlerAudit.Gate02.cutoff_ge_two
#check @ErdosMahlerAudit.Gate02.rho_lower
#print axioms ErdosMahlerAudit.Gate02.rho_lower
#check @ErdosMahlerAudit.Gate02.exceptional_density_upper
#print axioms ErdosMahlerAudit.Gate02.exceptional_density_upper
#check @ErdosMahlerAudit.Gate02.eventually_density_gap
#print axioms ErdosMahlerAudit.Gate02.eventually_density_gap

-- ErdosMahlerAudit/Gate02/AdmissibleChoices.lean
#check @ErdosMahlerAudit.Gate02.eventually_two_admissible
#print axioms ErdosMahlerAudit.Gate02.eventually_two_admissible
#check @ErdosMahlerAudit.Gate02.arbitrarily_large_two_admissible
#print axioms ErdosMahlerAudit.Gate02.arbitrarily_large_two_admissible
#check @ErdosMahlerAudit.Gate02.conditional_admissible_choices
#print axioms ErdosMahlerAudit.Gate02.conditional_admissible_choices
#check @ErdosMahlerAudit.Gate02.conditional_successors
#print axioms ErdosMahlerAudit.Gate02.conditional_successors
