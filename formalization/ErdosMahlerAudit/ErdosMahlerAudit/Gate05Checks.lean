module

public import ErdosMahlerAudit.Gate05.LogarithmicHeight

/-! Gate 05: complete declaration types, transparent bodies, and axiom audit. -/

set_option format.width 110

#print ErdosMahlerAudit.alpha
#print ErdosMahlerAudit.a
#print ErdosMahlerAudit.R
#print ErdosMahlerAudit.Exceptional
#print ErdosMahlerAudit.convergentDenominators
#print ErdosMahlerAudit.Gate02.badIndices
#print ErdosMahlerAudit.Gate02.E
#check @ErdosMahlerAudit.R_num
#print axioms ErdosMahlerAudit.R_num
#check @ErdosMahlerAudit.R_den
#print axioms ErdosMahlerAudit.R_den
#check @ErdosMahlerAudit.R_coprime
#print axioms ErdosMahlerAudit.R_coprime
#check @ErdosMahlerAudit.R_separation
#print axioms ErdosMahlerAudit.R_separation
#check @ErdosMahlerAudit.Gate03.convergentDenominators_unbounded
#print axioms ErdosMahlerAudit.Gate03.convergentDenominators_unbounded

-- Inspected pinned-library interfaces.
#check @Nat.coprime_div_gcd_div_gcd
#check @Nat.div_gcd_pos_of_pos_left
#check @Nat.div_gcd_pos_of_pos_right
#check @Nat.Prime.dvd_of_dvd_pow
#check @Nat.factorization_def
#check @Nat.factorization_mul
#check @Nat.factorization_pow
#check @Nat.eq_of_factorization_eq
#check @Nat.Prime.factorization_pow
#check @Real.rpow_sub
#check @Real.rpow_mul
#check @Real.mul_rpow
#check @Real.rpow_le_rpow_of_nonpos
#check @tendsto_rpow_atTop
#check @Set.Finite.bddAbove
#check @Finset.exists_mem_eq_sup
#check @Real.log_rpow
#check @tendsto_order

-- Arithmetic.lean
#check @ErdosMahlerAudit.Gate05.P
#print axioms ErdosMahlerAudit.Gate05.P
#print ErdosMahlerAudit.Gate05.P
#check @ErdosMahlerAudit.Gate05.S
#print axioms ErdosMahlerAudit.Gate05.S
#print ErdosMahlerAudit.Gate05.S
#check @ErdosMahlerAudit.Gate05.u
#print axioms ErdosMahlerAudit.Gate05.u
#print ErdosMahlerAudit.Gate05.u
#check @ErdosMahlerAudit.Gate05.v
#print axioms ErdosMahlerAudit.Gate05.v
#print ErdosMahlerAudit.Gate05.v
#check @ErdosMahlerAudit.Gate05.d
#print axioms ErdosMahlerAudit.Gate05.d
#print ErdosMahlerAudit.Gate05.d
#check @ErdosMahlerAudit.Gate05.U
#print axioms ErdosMahlerAudit.Gate05.U
#print ErdosMahlerAudit.Gate05.U
#check @ErdosMahlerAudit.Gate05.W
#print axioms ErdosMahlerAudit.Gate05.W
#print ErdosMahlerAudit.Gate05.W
#check @ErdosMahlerAudit.Gate05.e
#print axioms ErdosMahlerAudit.Gate05.e
#print ErdosMahlerAudit.Gate05.e
#check @ErdosMahlerAudit.Gate05.H
#print axioms ErdosMahlerAudit.Gate05.H
#print ErdosMahlerAudit.Gate05.H
#check @ErdosMahlerAudit.Gate05.P_pos
#print axioms ErdosMahlerAudit.Gate05.P_pos
#check @ErdosMahlerAudit.Gate05.S_pos
#print axioms ErdosMahlerAudit.Gate05.S_pos
#check @ErdosMahlerAudit.Gate05.v_pos
#print axioms ErdosMahlerAudit.Gate05.v_pos
#check @ErdosMahlerAudit.Gate05.u_cast
#print axioms ErdosMahlerAudit.Gate05.u_cast
#check @ErdosMahlerAudit.Gate05.u_pos
#print axioms ErdosMahlerAudit.Gate05.u_pos
#check @ErdosMahlerAudit.Gate05.uv_coprime
#print axioms ErdosMahlerAudit.Gate05.uv_coprime
#check @ErdosMahlerAudit.Gate05.canonical_real
#print axioms ErdosMahlerAudit.Gate05.canonical_real
#check @ErdosMahlerAudit.Gate05.u_le_two_v
#print axioms ErdosMahlerAudit.Gate05.u_le_two_v
#check @ErdosMahlerAudit.Gate05.R_eq_P_div_S
#print axioms ErdosMahlerAudit.Gate05.R_eq_P_div_S
#check @ErdosMahlerAudit.Gate05.S_lt_P_lt_two_S
#print axioms ErdosMahlerAudit.Gate05.S_lt_P_lt_two_S
#check @ErdosMahlerAudit.Gate05.d_pos
#print axioms ErdosMahlerAudit.Gate05.d_pos
#check @ErdosMahlerAudit.Gate05.U_pos
#print axioms ErdosMahlerAudit.Gate05.U_pos
#check @ErdosMahlerAudit.Gate05.W_pos
#print axioms ErdosMahlerAudit.Gate05.W_pos
#check @ErdosMahlerAudit.Gate05.UW_coprime
#print axioms ErdosMahlerAudit.Gate05.UW_coprime
#check @ErdosMahlerAudit.Gate05.d_mul_U
#print axioms ErdosMahlerAudit.Gate05.d_mul_U
#check @ErdosMahlerAudit.Gate05.d_mul_W
#print axioms ErdosMahlerAudit.Gate05.d_mul_W
#check @ErdosMahlerAudit.Gate05.d_prime_support
#print axioms ErdosMahlerAudit.Gate05.d_prime_support
#check @ErdosMahlerAudit.Gate05.cross_ne
#print axioms ErdosMahlerAudit.Gate05.cross_ne
#check @ErdosMahlerAudit.Gate05.e_pos
#print axioms ErdosMahlerAudit.Gate05.e_pos
#check @ErdosMahlerAudit.Gate05.U_ne_W
#print axioms ErdosMahlerAudit.Gate05.U_ne_W
#check @ErdosMahlerAudit.Gate05.H_le_two_S_v
#print axioms ErdosMahlerAudit.Gate05.H_le_two_S_v

-- SmoothPart.lean
#check @ErdosMahlerAudit.Gate05.smoothPart
#print axioms ErdosMahlerAudit.Gate05.smoothPart
#print ErdosMahlerAudit.Gate05.smoothPart
#check @ErdosMahlerAudit.Gate05.smoothPart_eq_padicValNat
#print axioms ErdosMahlerAudit.Gate05.smoothPart_eq_padicValNat
#check @ErdosMahlerAudit.Gate05.smoothPart_pos
#print axioms ErdosMahlerAudit.Gate05.smoothPart_pos
#check @ErdosMahlerAudit.Gate05.smoothPart_mul
#print axioms ErdosMahlerAudit.Gate05.smoothPart_mul
#check @ErdosMahlerAudit.Gate05.smoothPart_pow
#print axioms ErdosMahlerAudit.Gate05.smoothPart_pow
#check @ErdosMahlerAudit.Gate05.smoothPart_eq_self
#print axioms ErdosMahlerAudit.Gate05.smoothPart_eq_self
#check @ErdosMahlerAudit.Gate05.smoothPart_two_pow
#print axioms ErdosMahlerAudit.Gate05.smoothPart_two_pow
#check @ErdosMahlerAudit.Gate05.smoothPart_three_pow
#print axioms ErdosMahlerAudit.Gate05.smoothPart_three_pow
#check @ErdosMahlerAudit.Gate05.smoothPart_d
#print axioms ErdosMahlerAudit.Gate05.smoothPart_d
#check @ErdosMahlerAudit.Gate05.normalized_product
#print axioms ErdosMahlerAudit.Gate05.normalized_product
#check @ErdosMahlerAudit.Gate05.smoothPart_normalized_product
#print axioms ErdosMahlerAudit.Gate05.smoothPart_normalized_product

-- LocalProduct.lean
#check @ErdosMahlerAudit.Gate05.localProduct
#print axioms ErdosMahlerAudit.Gate05.localProduct
#print ErdosMahlerAudit.Gate05.localProduct
#check @ErdosMahlerAudit.Gate05.e_cast
#print axioms ErdosMahlerAudit.Gate05.e_cast
#check @ErdosMahlerAudit.Gate05.U_real
#print axioms ErdosMahlerAudit.Gate05.U_real
#check @ErdosMahlerAudit.Gate05.W_real
#print axioms ErdosMahlerAudit.Gate05.W_real
#check @ErdosMahlerAudit.Gate05.normalized_difference
#print axioms ErdosMahlerAudit.Gate05.normalized_difference
#check @ErdosMahlerAudit.Gate05.cross_error
#print axioms ErdosMahlerAudit.Gate05.cross_error
#check @ErdosMahlerAudit.Gate05.localProduct_identity
#print axioms ErdosMahlerAudit.Gate05.localProduct_identity
#check @ErdosMahlerAudit.Gate05.localProduct_le_error
#print axioms ErdosMahlerAudit.Gate05.localProduct_le_error
#check @ErdosMahlerAudit.Gate05.normalized_ratio_error
#print axioms ErdosMahlerAudit.Gate05.normalized_ratio_error

-- ExternalContract.lean
#check @ErdosMahlerAudit.Gate05.SubspaceTwoThreePrimitive
#print axioms ErdosMahlerAudit.Gate05.SubspaceTwoThreePrimitive
#print ErdosMahlerAudit.Gate05.SubspaceTwoThreePrimitive

-- HeightEstimates.lean
#check @ErdosMahlerAudit.Gate05.violation_den_lt
#print axioms ErdosMahlerAudit.Gate05.violation_den_lt
#check @ErdosMahlerAudit.Gate05.violation_height_lt
#print axioms ErdosMahlerAudit.Gate05.violation_height_lt
#check @ErdosMahlerAudit.Gate05.violation_product_lt
#print axioms ErdosMahlerAudit.Gate05.violation_product_lt
#check @ErdosMahlerAudit.Gate05.scale_power_bound
#print axioms ErdosMahlerAudit.Gate05.scale_power_bound
#check @ErdosMahlerAudit.Gate05.delta_bounds
#print axioms ErdosMahlerAudit.Gate05.delta_bounds
#check @ErdosMahlerAudit.Gate05.euclidean_power_bound
#print axioms ErdosMahlerAudit.Gate05.euclidean_power_bound
#check @ErdosMahlerAudit.Gate05.exists_euclidean_threshold
#print axioms ErdosMahlerAudit.Gate05.exists_euclidean_threshold

-- FinitePairs.lean
#check @ErdosMahlerAudit.Gate05.smallProductPairs
#print axioms ErdosMahlerAudit.Gate05.smallProductPairs
#print ErdosMahlerAudit.Gate05.smallProductPairs
#check @ErdosMahlerAudit.Gate05.smallProductPairs_finite
#print axioms ErdosMahlerAudit.Gate05.smallProductPairs_finite
#check @ErdosMahlerAudit.Gate05.violating_pair_mem
#print axioms ErdosMahlerAudit.Gate05.violating_pair_mem
#check @ErdosMahlerAudit.Gate05.finite_pair_gap
#print axioms ErdosMahlerAudit.Gate05.finite_pair_gap

-- HeightBound.lean
#check @ErdosMahlerAudit.Gate05.S_rpow
#print axioms ErdosMahlerAudit.Gate05.S_rpow
#check @ErdosMahlerAudit.Gate05.eventually_S_neg_lt
#print axioms ErdosMahlerAudit.Gate05.eventually_S_neg_lt
#check @ErdosMahlerAudit.Gate05.height_lower_S
#print axioms ErdosMahlerAudit.Gate05.height_lower_S
#check @ErdosMahlerAudit.Gate05.height_lower
#print axioms ErdosMahlerAudit.Gate05.height_lower

-- EscapingDenominators.lean
#check @ErdosMahlerAudit.Gate05.exceptional_power_bound
#print axioms ErdosMahlerAudit.Gate05.exceptional_power_bound
#check @ErdosMahlerAudit.Gate05.log_bound_of_power_bound
#print axioms ErdosMahlerAudit.Gate05.log_bound_of_power_bound
#check @ErdosMahlerAudit.Gate05.exceptional_log_sublinear
#print axioms ErdosMahlerAudit.Gate05.exceptional_log_sublinear

-- LogarithmicHeight.lean
#check @ErdosMahlerAudit.Gate05.exceptional_den_lt_three_pow
#print axioms ErdosMahlerAudit.Gate05.exceptional_den_lt_three_pow
#check @ErdosMahlerAudit.Gate05.exceptionalDenominators
#print axioms ErdosMahlerAudit.Gate05.exceptionalDenominators
#print ErdosMahlerAudit.Gate05.exceptionalDenominators
#check @ErdosMahlerAudit.Gate05.mem_exceptionalDenominators
#print axioms ErdosMahlerAudit.Gate05.mem_exceptionalDenominators
#check @ErdosMahlerAudit.Gate05.logarithmicHeight
#print axioms ErdosMahlerAudit.Gate05.logarithmicHeight
#print ErdosMahlerAudit.Gate05.logarithmicHeight
#check @ErdosMahlerAudit.Gate05.logarithmicHeight_nonneg
#print axioms ErdosMahlerAudit.Gate05.logarithmicHeight_nonneg
#check @ErdosMahlerAudit.Gate05.witness_log_le_height
#print axioms ErdosMahlerAudit.Gate05.witness_log_le_height
#check @ErdosMahlerAudit.Gate05.logarithmicHeight_eq_zero_or_witness
#print axioms ErdosMahlerAudit.Gate05.logarithmicHeight_eq_zero_or_witness
#check @ErdosMahlerAudit.Gate05.logarithmicHeight_le
#print axioms ErdosMahlerAudit.Gate05.logarithmicHeight_le
#check @ErdosMahlerAudit.Gate05.logarithmicHeight_zero_iff
#print axioms ErdosMahlerAudit.Gate05.logarithmicHeight_zero_iff
#check @ErdosMahlerAudit.Gate05.E_one_eq_zero_of_height_zero
#print axioms ErdosMahlerAudit.Gate05.E_one_eq_zero_of_height_zero
#check @ErdosMahlerAudit.Gate05.logarithmicHeight_sublinear
#print axioms ErdosMahlerAudit.Gate05.logarithmicHeight_sublinear
#check @ErdosMahlerAudit.Gate05.logarithmicHeight_div_tendsto_zero
#print axioms ErdosMahlerAudit.Gate05.logarithmicHeight_div_tendsto_zero

-- The external parameter is an ordinary argument, absent from axiom lists.
set_option pp.explicit true in
#check @ErdosMahlerAudit.Gate05.height_lower
set_option pp.explicit true in
#check @ErdosMahlerAudit.Gate05.exceptional_power_bound
set_option pp.explicit true in
#check @ErdosMahlerAudit.Gate05.exceptional_log_sublinear
set_option pp.explicit true in
#check @ErdosMahlerAudit.Gate05.logarithmicHeight_div_tendsto_zero

-- Boundary instances retain exact arithmetic and the external input.
open ErdosMahlerAudit ErdosMahlerAudit.Gate05
#check fun hST : SubspaceTwoThreePrimitive => height_lower hST 2 (by norm_num)
#check delta_bounds (ε := 4) (by norm_num)
#check smoothPart_normalized_product 0 (s := 1) (by norm_num)
#check logarithmicHeight_zero_iff
#check fun hST : SubspaceTwoThreePrimitive =>
  exceptional_log_sublinear hST 5 (by norm_num) (by norm_num)

example : Exceptional 5 5 1 := by
  have ha : a 5 = 8 := (exponent_unique (b := 5) (n := 8) (by norm_num)).symm
  norm_num [Exceptional, R, ha]
