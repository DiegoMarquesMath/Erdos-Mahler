module

public import ErdosMahlerAudit.Gate04.SmallDenominators

/-! Gate 04: reproducible definition, theorem-type and foundational-axiom audit. -/

set_option format.width 110

-- Existing objects and the arbitrary closed-interval input.
#print ErdosMahlerAudit.Exceptional
#print ErdosMahlerAudit.Gate02.E
#print ErdosMahlerAudit.Gate02.badIndices
#print ErdosMahlerAudit.convergentDenominators
#check @ErdosMahlerAudit.Phi_R
#print axioms ErdosMahlerAudit.Phi_R
#check @ErdosMahlerAudit.R_mem_Ioo
#print axioms ErdosMahlerAudit.R_mem_Ioo
#check @ErdosMahlerAudit.exceptionalCount_antitone
#print axioms ErdosMahlerAudit.exceptionalCount_antitone
#check @ErdosMahlerAudit.Gate03.rotation_closed_upper
#print axioms ErdosMahlerAudit.Gate03.rotation_closed_upper
#check @ErdosMahlerAudit.Gate02.E_eq_exceptionalCount
#print axioms ErdosMahlerAudit.Gate02.E_eq_exceptionalCount
#check @Rat.num_div_den
#print axioms Rat.num_div_den
#check @Rat.pos
#print axioms Rat.pos
#check @Rat.cast_def
#print axioms Rat.cast_def
#check @Nat.le_floor
#print axioms Nat.le_floor
#check @Nat.floor_le
#print axioms Nat.floor_le
#check @Finset.card_biUnion_le
#print axioms Finset.card_biUnion_le
#check @Real.log_le_sub_one_of_pos
#print axioms Real.log_le_sub_one_of_pos
#check @Real.one_sub_inv_le_log_of_pos
#print axioms Real.one_sub_inv_le_log_of_pos
#check @Real.rpow_le_rpow_of_nonpos
#print axioms Real.rpow_le_rpow_of_nonpos
#check @Real.rpow_le_rpow_of_exponent_le
#print axioms Real.rpow_le_rpow_of_exponent_le
#check @Real.rpow_mul
#print axioms Real.rpow_mul
#check @Real.mul_rpow
#print axioms Real.mul_rpow
#check @Nat.find_spec
#print axioms Nat.find_spec
#check @Nat.find_min
#print axioms Nat.find_min
#check @pow_unbounded_of_one_lt
#print axioms pow_unbounded_of_one_lt

-- RationalGrid.lean
#check @ErdosMahlerAudit.Gate04.numeratorDenominatorGrid
#print axioms ErdosMahlerAudit.Gate04.numeratorDenominatorGrid
#print ErdosMahlerAudit.Gate04.numeratorDenominatorGrid
#check @ErdosMahlerAudit.Gate04.rationalShell
#print axioms ErdosMahlerAudit.Gate04.rationalShell
#print ErdosMahlerAudit.Gate04.rationalShell
#check @ErdosMahlerAudit.Gate04.canonical_num_bounds
#print axioms ErdosMahlerAudit.Gate04.canonical_num_bounds
#check @ErdosMahlerAudit.Gate04.canonical_pair_mem_grid
#print axioms ErdosMahlerAudit.Gate04.canonical_pair_mem_grid
#check @ErdosMahlerAudit.Gate04.mem_rationalShell
#print axioms ErdosMahlerAudit.Gate04.mem_rationalShell
#check @ErdosMahlerAudit.Gate04.numeratorDenominatorGrid_card_le
#print axioms ErdosMahlerAudit.Gate04.numeratorDenominatorGrid_card_le
#check @ErdosMahlerAudit.Gate04.rationalShell_card_le
#print axioms ErdosMahlerAudit.Gate04.rationalShell_card_le

-- Neighborhood.lean
#check @ErdosMahlerAudit.Gate04.exceptionalRadius
#print axioms ErdosMahlerAudit.Gate04.exceptionalRadius
#print ErdosMahlerAudit.Gate04.exceptionalRadius
#check @ErdosMahlerAudit.Gate04.clippedLower
#print axioms ErdosMahlerAudit.Gate04.clippedLower
#print ErdosMahlerAudit.Gate04.clippedLower
#check @ErdosMahlerAudit.Gate04.clippedUpper
#print axioms ErdosMahlerAudit.Gate04.clippedUpper
#print ErdosMahlerAudit.Gate04.clippedUpper
#check @ErdosMahlerAudit.Gate04.witnessIndices
#print axioms ErdosMahlerAudit.Gate04.witnessIndices
#print ErdosMahlerAudit.Gate04.witnessIndices
#check @ErdosMahlerAudit.Gate04.exceptionalRadius_pos
#print axioms ErdosMahlerAudit.Gate04.exceptionalRadius_pos
#check @ErdosMahlerAudit.Gate04.Phi_difference_bounds
#print axioms ErdosMahlerAudit.Gate04.Phi_difference_bounds
#check @ErdosMahlerAudit.Gate04.clipped_bounds
#print axioms ErdosMahlerAudit.Gate04.clipped_bounds
#check @ErdosMahlerAudit.Gate04.exceptional_mem_clipped
#print axioms ErdosMahlerAudit.Gate04.exceptional_mem_clipped
#check @ErdosMahlerAudit.Gate04.exceptional_fract_mem_closed
#print axioms ErdosMahlerAudit.Gate04.exceptional_fract_mem_closed
#check @ErdosMahlerAudit.Gate04.clipped_image_length
#print axioms ErdosMahlerAudit.Gate04.clipped_image_length
#check @ErdosMahlerAudit.Gate04.witnessIndices_card_le
#print axioms ErdosMahlerAudit.Gate04.witnessIndices_card_le
#check @ErdosMahlerAudit.Gate04.witnessIndices_card_le_shell
#print axioms ErdosMahlerAudit.Gate04.witnessIndices_card_le_shell

-- ShellCounting.lean
#check @ErdosMahlerAudit.Gate04.shellIndices
#print axioms ErdosMahlerAudit.Gate04.shellIndices
#print ErdosMahlerAudit.Gate04.shellIndices
#check @ErdosMahlerAudit.Gate04.shellIndices_eq_biUnion
#print axioms ErdosMahlerAudit.Gate04.shellIndices_eq_biUnion
#check @ErdosMahlerAudit.Gate04.shellIndices_card_le_sum
#print axioms ErdosMahlerAudit.Gate04.shellIndices_card_le_sum
#check @ErdosMahlerAudit.Gate04.shellIndices_card_le
#print axioms ErdosMahlerAudit.Gate04.shellIndices_card_le

-- DyadicDecomposition.lean
#check @ErdosMahlerAudit.Gate04.dyadicScale
#print axioms ErdosMahlerAudit.Gate04.dyadicScale
#print ErdosMahlerAudit.Gate04.dyadicScale
#check @ErdosMahlerAudit.Gate04.dyadicScale_zero
#print axioms ErdosMahlerAudit.Gate04.dyadicScale_zero
#check @ErdosMahlerAudit.Gate04.dyadicScale_succ
#print axioms ErdosMahlerAudit.Gate04.dyadicScale_succ
#check @ErdosMahlerAudit.Gate04.dyadicScale_pos
#print axioms ErdosMahlerAudit.Gate04.dyadicScale_pos
#check @ErdosMahlerAudit.Gate04.le_dyadicScale
#print axioms ErdosMahlerAudit.Gate04.le_dyadicScale
#check @ErdosMahlerAudit.Gate04.exists_dyadic_cutoff
#print axioms ErdosMahlerAudit.Gate04.exists_dyadic_cutoff
#check @ErdosMahlerAudit.Gate04.dyadic_cover
#print axioms ErdosMahlerAudit.Gate04.dyadic_cover
#check @ErdosMahlerAudit.Gate04.dyadic_ratio_le_quarter
#print axioms ErdosMahlerAudit.Gate04.dyadic_ratio_le_quarter
#check @ErdosMahlerAudit.Gate04.geometric_sum_le_four_thirds
#print axioms ErdosMahlerAudit.Gate04.geometric_sum_le_four_thirds
#check @ErdosMahlerAudit.Gate04.dyadicScale_rpow
#print axioms ErdosMahlerAudit.Gate04.dyadicScale_rpow
#check @ErdosMahlerAudit.Gate04.dyadic_negative_sum
#print axioms ErdosMahlerAudit.Gate04.dyadic_negative_sum
#check @ErdosMahlerAudit.Gate04.dyadic_square_sum_identity
#print axioms ErdosMahlerAudit.Gate04.dyadic_square_sum_identity
#check @ErdosMahlerAudit.Gate04.dyadic_square_sum
#print axioms ErdosMahlerAudit.Gate04.dyadic_square_sum

-- TruncatedCounting.lean
#check @ErdosMahlerAudit.Gate04.boundedIndices
#print axioms ErdosMahlerAudit.Gate04.boundedIndices
#print ErdosMahlerAudit.Gate04.boundedIndices
#check @ErdosMahlerAudit.Gate04.boundedIndices_empty
#print axioms ErdosMahlerAudit.Gate04.boundedIndices_empty
#check @ErdosMahlerAudit.Gate04.boundedIndices_eq_truncated_union
#print axioms ErdosMahlerAudit.Gate04.boundedIndices_eq_truncated_union
#check @ErdosMahlerAudit.Gate04.truncatedIndices_subset_shell
#print axioms ErdosMahlerAudit.Gate04.truncatedIndices_subset_shell
#check @ErdosMahlerAudit.Gate04.boundedIndices_card_le_sum
#print axioms ErdosMahlerAudit.Gate04.boundedIndices_card_le_sum
#check @ErdosMahlerAudit.Gate04.boundedIndices_card_le
#print axioms ErdosMahlerAudit.Gate04.boundedIndices_card_le
#check @ErdosMahlerAudit.Gate04.E_le_high_add_bounded
#print axioms ErdosMahlerAudit.Gate04.E_le_high_add_bounded

-- SmallDenominators.lean
#check @ErdosMahlerAudit.Gate04.E_le_of_cutoff_le
#print axioms ErdosMahlerAudit.Gate04.E_le_of_cutoff_le
#check @ErdosMahlerAudit.Gate04.small_denominator_estimate
#print axioms ErdosMahlerAudit.Gate04.small_denominator_estimate
#check @ErdosMahlerAudit.Gate04.small_denominator_absolute
#print axioms ErdosMahlerAudit.Gate04.small_denominator_absolute

-- Explicit arguments on the exact final existential contract.
set_option pp.explicit true in
#check @ErdosMahlerAudit.Gate04.small_denominator_absolute

-- Boundary applications, elaborated in the pinned environment.
open ErdosMahlerAudit ErdosMahlerAudit.Gate04
#check (mem_rationalShell (V := (5 / 2 : ℝ)) (s := (4 / 3 : ℚ))).mpr
  (by
    have hd' := Rat.den_div_eq_of_coprime (a := (4 : ℤ)) (b := (3 : ℤ))
      (by norm_num) (by decide)
    have hdZ : ((4 / 3 : ℚ).den : ℤ) = 3 := by
      simpa only [Int.cast_ofNat] using hd'
    have hd : (4 / 3 : ℚ).den = 3 := Int.natCast_inj.mp hdZ
    norm_num [hd])
#check dyadic_cover (D := 2) (U := 8) (v := 8) (k := 2)
  (by norm_num) (by norm_num) (by norm_num [dyadicScale])
#check dyadic_cover (D := 5 / 2) (U := 9) (v := 9) (k := 2)
  (by norm_num) (by norm_num) (by norm_num [dyadicScale])
#check dyadic_ratio_le_quarter (ν := 4) (by norm_num)
#check boundedIndices_empty (N := 1) (D := 2) (U := 2) (ν := 5) (by norm_num)
#check boundedIndices_empty (N := 1) (D := 2) (U := 1) (ν := 5) (by norm_num)
#check small_denominator_estimate Gate03.one_mem_convergentDenominators
  (ν := 5) (D := 2) (by norm_num) (by norm_num)
