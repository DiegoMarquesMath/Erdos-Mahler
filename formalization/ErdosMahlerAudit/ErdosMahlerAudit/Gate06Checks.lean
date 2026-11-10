module

public import ErdosMahlerAudit.Gate06.ProductTransfer

/-! Gate 06 declaration, definition-body, ordinary-argument and axiom audit. -/

set_option format.width 110

-- Unchanged manuscript objects and the arbitrary-witness input.
#print ErdosMahlerAudit.alpha
#print ErdosMahlerAudit.a
#print ErdosMahlerAudit.R
#print ErdosMahlerAudit.Exceptional
#print ErdosMahlerAudit.convergentDenominators
#check @ErdosMahlerAudit.Gate04.witnessIndices_card_le
#print axioms ErdosMahlerAudit.Gate04.witnessIndices_card_le
#check @ErdosMahlerAudit.rational_separation
#print axioms ErdosMahlerAudit.rational_separation
#check @Rat.mul_den_dvd
#check @Nat.ceil_add_le
#check @Finset.card_eq_sum_card_image
#check @Finset.card_le_card_of_injective
#check @Real.rpow_lt_rpow
#check @Real.rpow_mul
#check @Real.rpow_le_rpow_of_exponent_le
#check @Real.rpow_lt_rpow_of_exponent_lt

-- Band.lean
#check @ErdosMahlerAudit.Gate06.V
#print axioms ErdosMahlerAudit.Gate06.V
#print ErdosMahlerAudit.Gate06.V
#check @ErdosMahlerAudit.Gate06.H
#print axioms ErdosMahlerAudit.Gate06.H
#print ErdosMahlerAudit.Gate06.H
#check @ErdosMahlerAudit.Gate06.exceptionalBand
#print axioms ErdosMahlerAudit.Gate06.exceptionalBand
#print ErdosMahlerAudit.Gate06.exceptionalBand
#check @ErdosMahlerAudit.Gate06.mem_exceptionalBand
#print axioms ErdosMahlerAudit.Gate06.mem_exceptionalBand
#check @ErdosMahlerAudit.Gate06.selectedFraction
#print axioms ErdosMahlerAudit.Gate06.selectedFraction
#print ErdosMahlerAudit.Gate06.selectedFraction
#check @ErdosMahlerAudit.Gate06.selectedFraction_spec
#print axioms ErdosMahlerAudit.Gate06.selectedFraction_spec
#check @ErdosMahlerAudit.Gate06.selectedFractions
#print axioms ErdosMahlerAudit.Gate06.selectedFractions
#print ErdosMahlerAudit.Gate06.selectedFractions
#check @ErdosMahlerAudit.Gate06.selectedProductSet
#print axioms ErdosMahlerAudit.Gate06.selectedProductSet
#print ErdosMahlerAudit.Gate06.selectedProductSet
#check @ErdosMahlerAudit.Gate06.prescribedProductSet
#print axioms ErdosMahlerAudit.Gate06.prescribedProductSet
#print ErdosMahlerAudit.Gate06.prescribedProductSet
#check @ErdosMahlerAudit.Gate06.selectedProductSet_eq_image
#print axioms ErdosMahlerAudit.Gate06.selectedProductSet_eq_image
#check @ErdosMahlerAudit.Gate06.selectedFractions_positive
#print axioms ErdosMahlerAudit.Gate06.selectedFractions_positive
#check @ErdosMahlerAudit.Gate06.selected_sets_empty
#print axioms ErdosMahlerAudit.Gate06.selected_sets_empty

-- Multiplicity.lean
#check @ErdosMahlerAudit.Gate06.denominator_decay
#print axioms ErdosMahlerAudit.Gate06.denominator_decay
#check @ErdosMahlerAudit.Gate06.selected_fiber_card_le
#print axioms ErdosMahlerAudit.Gate06.selected_fiber_card_le
#check @ErdosMahlerAudit.Gate06.exceptional_band_multiplicity
#print axioms ErdosMahlerAudit.Gate06.exceptional_band_multiplicity

-- PrescribedProducts.lean
#check @ErdosMahlerAudit.Gate06.prescribed_product_formula
#print axioms ErdosMahlerAudit.Gate06.prescribed_product_formula
#check @ErdosMahlerAudit.Gate06.ceiling_sum_two_values
#print axioms ErdosMahlerAudit.Gate06.ceiling_sum_two_values
#check @ErdosMahlerAudit.Gate06.index_sum_mem
#print axioms ErdosMahlerAudit.Gate06.index_sum_mem
#check @ErdosMahlerAudit.Gate06.prescribedProductSet_card_le
#print axioms ErdosMahlerAudit.Gate06.prescribedProductSet_card_le

-- Separation.lean
#check @ErdosMahlerAudit.Gate06.V_pos
#print axioms ErdosMahlerAudit.Gate06.V_pos
#check @ErdosMahlerAudit.Gate06.H_pos
#print axioms ErdosMahlerAudit.Gate06.H_pos
#check @ErdosMahlerAudit.Gate06.V_gt_one
#print axioms ErdosMahlerAudit.Gate06.V_gt_one
#check @ErdosMahlerAudit.Gate06.H_eq_V_rpow
#print axioms ErdosMahlerAudit.Gate06.H_eq_V_rpow
#check @ErdosMahlerAudit.Gate06.product_den_le
#print axioms ErdosMahlerAudit.Gate06.product_den_le
#check @ErdosMahlerAudit.Gate06.product_den_le_square
#print axioms ErdosMahlerAudit.Gate06.product_den_le_square
#check @ErdosMahlerAudit.Gate06.bounded_product_separation
#print axioms ErdosMahlerAudit.Gate06.bounded_product_separation
#check @ErdosMahlerAudit.Gate06.power_gap
#print axioms ErdosMahlerAudit.Gate06.power_gap
#check @ErdosMahlerAudit.Gate06.half_power_gap
#print axioms ErdosMahlerAudit.Gate06.half_power_gap

-- ProductError.lean
#check @ErdosMahlerAudit.Gate06.exceptional_error_at_cutoff
#print axioms ErdosMahlerAudit.Gate06.exceptional_error_at_cutoff
#check @ErdosMahlerAudit.Gate06.product_error_bound
#print axioms ErdosMahlerAudit.Gate06.product_error_bound
#check @ErdosMahlerAudit.Gate06.exceptional_product_error
#print axioms ErdosMahlerAudit.Gate06.exceptional_product_error
#check @ErdosMahlerAudit.Gate06.selected_product_error
#print axioms ErdosMahlerAudit.Gate06.selected_product_error
#check @ErdosMahlerAudit.Gate06.equal_prescribed_products_error
#print axioms ErdosMahlerAudit.Gate06.equal_prescribed_products_error

-- ProductTransfer.lean
#check @ErdosMahlerAudit.Gate06.selected_product_den_le
#print axioms ErdosMahlerAudit.Gate06.selected_product_den_le
#check @ErdosMahlerAudit.Gate06.prescribed_equality_forces_selected_equality
#print axioms ErdosMahlerAudit.Gate06.prescribed_equality_forces_selected_equality
#check @ErdosMahlerAudit.Gate06.card_image_le_of_fibers
#print axioms ErdosMahlerAudit.Gate06.card_image_le_of_fibers
#check @ErdosMahlerAudit.Gate06.selectedProductSet_card_le_prescribed
#print axioms ErdosMahlerAudit.Gate06.selectedProductSet_card_le_prescribed
#check @ErdosMahlerAudit.Gate06.exceptional_product_card_le
#print axioms ErdosMahlerAudit.Gate06.exceptional_product_card_le

-- Fully explicit final types: ordinary hypotheses are part of this audit.
set_option pp.explicit true in
#check @ErdosMahlerAudit.Gate06.exceptional_band_multiplicity
set_option pp.explicit true in
#check @ErdosMahlerAudit.Gate06.exceptional_product_card_le
#print ErdosMahlerAudit.Gate06.exceptional_band_multiplicity
#print ErdosMahlerAudit.Gate06.exceptional_product_card_le

-- Boundary instances, checked without any assumed exceptional witnesses.
open ErdosMahlerAudit ErdosMahlerAudit.Gate06
#check (show exceptionalBand 0 5 (9 / 8) 1 = ∅ from by simp [exceptionalBand])
#check (show selectedProductSet 0 5 (9 / 8) 1 = ∅ from
  (selected_sets_empty (by simp [exceptionalBand])).2)
#check denominator_decay (N := 1) (ν := 5) (v := 2)
  (by norm_num) (by norm_num) (by norm_num)
#check ceiling_sum_two_values 0 0
#check exceptional_band_multiplicity 1 5 (9 / 8) 1
  Gate03.one_mem_convergentDenominators (by norm_num) (by norm_num)
  (by norm_num) (by norm_num) (by norm_num)
#check exceptional_product_card_le 1 5 (9 / 8) 1
  Gate03.one_mem_convergentDenominators (by norm_num) (by norm_num)
  (by norm_num) (by norm_num) (by norm_num)
#check (show ((3 / 2 : ℚ) * (4 / 3 : ℚ)).den = 1 from by
  rw [show (3 / 2 : ℚ) * (4 / 3 : ℚ) = 2 by norm_num]
  norm_num)
#check card_image_le_of_fibers ({0, 1} : Finset ℕ)
  (fun _ => (1 : ℚ)) (fun _ => (2 : ℚ)) (by intros; rfl)
