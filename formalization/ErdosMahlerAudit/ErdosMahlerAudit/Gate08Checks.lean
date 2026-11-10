module

public import ErdosMahlerAudit.Gate08.Counting

/-! Gate08: all explicit declaration types, bodies, and foundational dependencies. -/

set_option format.width 110

-- Selection.lean
#check @ErdosMahlerAudit.Gate08.representative
#print axioms ErdosMahlerAudit.Gate08.representative
#print ErdosMahlerAudit.Gate08.representative
#check @ErdosMahlerAudit.Gate08.representative_spec
#print axioms ErdosMahlerAudit.Gate08.representative_spec
#check @ErdosMahlerAudit.Gate08.representative_injective
#print axioms ErdosMahlerAudit.Gate08.representative_injective
#check @ErdosMahlerAudit.Gate08.selectedLift
#print axioms ErdosMahlerAudit.Gate08.selectedLift
#print ErdosMahlerAudit.Gate08.selectedLift
#check @ErdosMahlerAudit.Gate08.selectedLift_value
#print axioms ErdosMahlerAudit.Gate08.selectedLift_value
#check @ErdosMahlerAudit.Gate08.selectedLift_mem
#print axioms ErdosMahlerAudit.Gate08.selectedLift_mem
#check @ErdosMahlerAudit.Gate08.selected_root
#print axioms ErdosMahlerAudit.Gate08.selected_root
#check @ErdosMahlerAudit.Gate08.selectedFiber
#print axioms ErdosMahlerAudit.Gate08.selectedFiber
#print ErdosMahlerAudit.Gate08.selectedFiber
#check @ErdosMahlerAudit.Gate08.selectedFiber_nonempty_iff
#print axioms ErdosMahlerAudit.Gate08.selectedFiber_nonempty_iff

-- Height.lean
#check @ErdosMahlerAudit.Gate08.rationalHeight
#print axioms ErdosMahlerAudit.Gate08.rationalHeight
#print ErdosMahlerAudit.Gate08.rationalHeight
#check @ErdosMahlerAudit.Gate08.rationalHeight_eq_library
#print axioms ErdosMahlerAudit.Gate08.rationalHeight_eq_library
#check @ErdosMahlerAudit.Gate08.rationalHeight_pow
#print axioms ErdosMahlerAudit.Gate08.rationalHeight_pow
#check @ErdosMahlerAudit.Gate08.rationalHeight_inv
#print axioms ErdosMahlerAudit.Gate08.rationalHeight_inv
#check @ErdosMahlerAudit.Gate08.rationalHeight_mul
#print axioms ErdosMahlerAudit.Gate08.rationalHeight_mul
#check @ErdosMahlerAudit.Gate08.rationalHeight_div
#print axioms ErdosMahlerAudit.Gate08.rationalHeight_div
#check @ErdosMahlerAudit.Gate08.numerator_cast
#print axioms ErdosMahlerAudit.Gate08.numerator_cast
#check @ErdosMahlerAudit.Gate08.log_two_le_height
#print axioms ErdosMahlerAudit.Gate08.log_two_le_height
#check @ErdosMahlerAudit.Gate08.abs_log_le_height
#print axioms ErdosMahlerAudit.Gate08.abs_log_le_height
#check @ErdosMahlerAudit.Gate08.selected_numerator_le
#print axioms ErdosMahlerAudit.Gate08.selected_numerator_le
#check @ErdosMahlerAudit.Gate08.selected_ratio_height
#print axioms ErdosMahlerAudit.Gate08.selected_ratio_height
#check @ErdosMahlerAudit.Gate08.two_w_add_log_two_le
#print axioms ErdosMahlerAudit.Gate08.two_w_add_log_two_le
#check @ErdosMahlerAudit.Gate08.selected_root_height
#print axioms ErdosMahlerAudit.Gate08.selected_root_height
#check @ErdosMahlerAudit.Gate08.MatveevRationalThree
#print axioms ErdosMahlerAudit.Gate08.MatveevRationalThree
#print ErdosMahlerAudit.Gate08.MatveevRationalThree

-- PowerSize.lean
#check @ErdosMahlerAudit.Gate08.exists_power_above
#print axioms ErdosMahlerAudit.Gate08.exists_power_above
#check @ErdosMahlerAudit.Gate08.leastExponent
#print axioms ErdosMahlerAudit.Gate08.leastExponent
#print ErdosMahlerAudit.Gate08.leastExponent
#check @ErdosMahlerAudit.Gate08.leastPower
#print axioms ErdosMahlerAudit.Gate08.leastPower
#print ErdosMahlerAudit.Gate08.leastPower
#check @ErdosMahlerAudit.Gate08.leastExponent_spec
#print axioms ErdosMahlerAudit.Gate08.leastExponent_spec
#check @ErdosMahlerAudit.Gate08.leastExponent_min
#print axioms ErdosMahlerAudit.Gate08.leastExponent_min
#check @ErdosMahlerAudit.Gate08.leastExponent_pos
#print axioms ErdosMahlerAudit.Gate08.leastExponent_pos
#check @ErdosMahlerAudit.Gate08.leastPower_bounds
#print axioms ErdosMahlerAudit.Gate08.leastPower_bounds
#check @ErdosMahlerAudit.Gate08.leastPower_pos
#print axioms ErdosMahlerAudit.Gate08.leastPower_pos
#check @ErdosMahlerAudit.Gate08.leastPower_log
#print axioms ErdosMahlerAudit.Gate08.leastPower_log
#check @ErdosMahlerAudit.Gate08.leastExponent_log_bound
#print axioms ErdosMahlerAudit.Gate08.leastExponent_log_bound

-- LogError.lean
#check @ErdosMahlerAudit.Gate08.linearForm
#print axioms ErdosMahlerAudit.Gate08.linearForm
#print ErdosMahlerAudit.Gate08.linearForm
#check @ErdosMahlerAudit.Gate08.log_lipschitz_one
#print axioms ErdosMahlerAudit.Gate08.log_lipschitz_one
#check @ErdosMahlerAudit.Gate08.selected_log_error
#print axioms ErdosMahlerAudit.Gate08.selected_log_error
#check @ErdosMahlerAudit.Gate08.linearForm_identity
#print axioms ErdosMahlerAudit.Gate08.linearForm_identity
#check @ErdosMahlerAudit.Gate08.selected_linearForm_small
#print axioms ErdosMahlerAudit.Gate08.selected_linearForm_small
#check @ErdosMahlerAudit.Gate08.ratio_eq_of_linearForm_zero
#print axioms ErdosMahlerAudit.Gate08.ratio_eq_of_linearForm_zero

-- Valuation.lean
#check @ErdosMahlerAudit.Gate08.valuation_R
#print axioms ErdosMahlerAudit.Gate08.valuation_R
#check @ErdosMahlerAudit.Gate08.valuation_R_ratio
#print axioms ErdosMahlerAudit.Gate08.valuation_R_ratio
#check @ErdosMahlerAudit.Gate08.valuation_nat_log_bound
#print axioms ErdosMahlerAudit.Gate08.valuation_nat_log_bound
#check @ErdosMahlerAudit.Gate08.valuation_height_bound
#print axioms ErdosMahlerAudit.Gate08.valuation_height_bound
#check @ErdosMahlerAudit.Gate08.index_gap_of_ratio_eq
#print axioms ErdosMahlerAudit.Gate08.index_gap_of_ratio_eq

-- Weighted.lean
#check @ErdosMahlerAudit.Gate08.weightedSize
#print axioms ErdosMahlerAudit.Gate08.weightedSize
#print ErdosMahlerAudit.Gate08.weightedSize
#check @ErdosMahlerAudit.Gate08.band_coefficient_bounds
#print axioms ErdosMahlerAudit.Gate08.band_coefficient_bounds
#check @ErdosMahlerAudit.Gate08.weightedSize_bounds
#print axioms ErdosMahlerAudit.Gate08.weightedSize_bounds
#check @ErdosMahlerAudit.Gate08.large_x_implies_w_le
#print axioms ErdosMahlerAudit.Gate08.large_x_implies_w_le
#check @ErdosMahlerAudit.Gate08.weightedSize_log_bound
#print axioms ErdosMahlerAudit.Gate08.weightedSize_log_bound

-- Rigidity.lean
#check @ErdosMahlerAudit.Gate08.matveevConstant
#print axioms ErdosMahlerAudit.Gate08.matveevConstant
#print ErdosMahlerAudit.Gate08.matveevConstant
#check @ErdosMahlerAudit.Gate08.matveevConstant_pos
#print axioms ErdosMahlerAudit.Gate08.matveevConstant_pos
#check @ErdosMahlerAudit.Gate08.matveev_specialization
#print axioms ErdosMahlerAudit.Gate08.matveev_specialization
#check @ErdosMahlerAudit.Gate08.rigidityThreshold
#print axioms ErdosMahlerAudit.Gate08.rigidityThreshold
#print ErdosMahlerAudit.Gate08.rigidityThreshold
#check @ErdosMahlerAudit.Gate08.rigidityThreshold_pos
#print axioms ErdosMahlerAudit.Gate08.rigidityThreshold_pos
#check @ErdosMahlerAudit.Gate08.selected_linearForm_zero
#print axioms ErdosMahlerAudit.Gate08.selected_linearForm_zero
#check @ErdosMahlerAudit.Gate08.ratio_rigidity_at_threshold
#print axioms ErdosMahlerAudit.Gate08.ratio_rigidity_at_threshold
#check @ErdosMahlerAudit.Gate08.same_class_ratio_rigidity
#print axioms ErdosMahlerAudit.Gate08.same_class_ratio_rigidity
#check @ErdosMahlerAudit.Gate08.index_gap_at_threshold
#print axioms ErdosMahlerAudit.Gate08.index_gap_at_threshold
#check @ErdosMahlerAudit.Gate08.same_class_index_gap
#print axioms ErdosMahlerAudit.Gate08.same_class_index_gap

-- Counting.lean
#check @ErdosMahlerAudit.Gate08.selectedFiber_card_at_threshold
#print axioms ErdosMahlerAudit.Gate08.selectedFiber_card_at_threshold
#check @ErdosMahlerAudit.Gate08.selected_class_card_le
#print axioms ErdosMahlerAudit.Gate08.selected_class_card_le

-- Exact pinned height, valuation, and quotient inputs.
#check @Rat.logHeight₁_eq_log_max
#print axioms Rat.logHeight₁_eq_log_max
#check @Height.logHeight₁_pow
#print axioms Height.logHeight₁_pow
#check @Height.logHeight₁_inv
#print axioms Height.logHeight₁_inv
#check @Height.logHeight₁_mul_le
#print axioms Height.logHeight₁_mul_le
#check @Rat.den_inv_of_ne_zero
#print axioms Rat.den_inv_of_ne_zero
#check @padicValRat.div
#print axioms padicValRat.div
#check @padicValRat.pow
#print axioms padicValRat.pow
#check @pow_padicValNat_dvd
#print axioms pow_padicValNat_dvd
#check @Int.card_Icc_of_le
#print axioms Int.card_Icc_of_le
#check @ErdosMahlerAudit.Gate07.rational_power_class_eq_iff
#print axioms ErdosMahlerAudit.Gate07.rational_power_class_eq_iff

-- All ordinary final-theorem arguments are displayed above; print their proof terms too.
#print ErdosMahlerAudit.Gate08.same_class_ratio_rigidity
#print ErdosMahlerAudit.Gate08.same_class_index_gap
#print ErdosMahlerAudit.Gate08.selected_class_card_le

open ErdosMahlerAudit ErdosMahlerAudit.Gate08 ErdosMahlerAudit.Gate07

-- Exact real endpoints: x=2 is itself a power boundary (q=4).
#check (show leastExponent 2 = 2 from by
  apply le_antisymm
  · by_contra h
    have hm := leastExponent_min (x := 2) (j := 2) (by omega)
    norm_num at hm
  · have hm := leastExponent_spec 2
    by_contra h
    have he : leastExponent 2 = 0 ∨ leastExponent 2 = 1 := by omega
    rcases he with he | he <;> rw [he] at hm <;> norm_num at hm)
#check leastPower_bounds (x := 2) (by norm_num)
#check (show rationalHeight (3 / 2 : ℚ) = Real.log 3 from by norm_num [rationalHeight])
#check rationalHeight_pow (3 / 2 : ℚ) 4
#check valuation_R_ratio 0 1
#check (show selectedFiber 0 5 (9 / 8) 1 4 (classMap 4 (0 : PositiveRatAdd)) = ∅ from by
  classical
  simp [selectedFiber, selectedPositive, Gate06.selectedFractions, Gate06.exceptionalBand])
