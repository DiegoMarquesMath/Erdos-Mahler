module

public import ErdosMahlerAudit.Gate07.PositiveRationals

/-! Gate 07: full types, transparent bodies, foundational dependencies, and boundaries. -/

set_option format.width 110

-- Pinned combinatorial inputs: full types including the NNRat codomain.
set_option pp.explicit true in
#check @Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add
#print axioms Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add
#check @Finset.ruzsa_triangle_inequality_sub_sub_sub
#print axioms Finset.ruzsa_triangle_inequality_sub_sub_sub
#check @QuotientAddGroup.eq_iff_sub_mem
#print axioms QuotientAddGroup.eq_iff_sub_mem
#check @eq_of_nsmul_eq_nsmul_of_addCommute
#check @NNRat.cast_le
#check @NNRat.cast_div
#check @Finset.nsmul
#print Finset.nsmul
#check @ErdosMahlerAudit.Gate06.exceptional_product_card_le
#print axioms ErdosMahlerAudit.Gate06.exceptional_product_card_le
#check @ErdosMahlerAudit.Gate06.selectedFractions_positive
#print axioms ErdosMahlerAudit.Gate06.selectedFractions_positive

-- Classes.lean
#check @ErdosMahlerAudit.Gate07.dilate
#print axioms ErdosMahlerAudit.Gate07.dilate
#print ErdosMahlerAudit.Gate07.dilate
#check @ErdosMahlerAudit.Gate07.multipleSubgroup
#print axioms ErdosMahlerAudit.Gate07.multipleSubgroup
#print ErdosMahlerAudit.Gate07.multipleSubgroup
#check @ErdosMahlerAudit.Gate07.classMap
#print axioms ErdosMahlerAudit.Gate07.classMap
#print ErdosMahlerAudit.Gate07.classMap
#check @ErdosMahlerAudit.Gate07.classImage
#print axioms ErdosMahlerAudit.Gate07.classImage
#print ErdosMahlerAudit.Gate07.classImage
#check @ErdosMahlerAudit.Gate07.class_eq_iff
#print axioms ErdosMahlerAudit.Gate07.class_eq_iff
#check @ErdosMahlerAudit.Gate07.class_dilate_sub
#print axioms ErdosMahlerAudit.Gate07.class_dilate_sub
#check @ErdosMahlerAudit.Gate07.translated_dilates_disjoint
#print axioms ErdosMahlerAudit.Gate07.translated_dilates_disjoint
#check @ErdosMahlerAudit.Gate07.dilation_injective
#print axioms ErdosMahlerAudit.Gate07.dilation_injective
#check @ErdosMahlerAudit.Gate07.dilate_card
#print axioms ErdosMahlerAudit.Gate07.dilate_card
#check @ErdosMahlerAudit.Gate07.translated_dilate_card
#print axioms ErdosMahlerAudit.Gate07.translated_dilate_card
#check @ErdosMahlerAudit.Gate07.class_card_mul_le
#print axioms ErdosMahlerAudit.Gate07.class_card_mul_le
#check @ErdosMahlerAudit.Gate07.classImage_empty
#print axioms ErdosMahlerAudit.Gate07.classImage_empty
#check @ErdosMahlerAudit.Gate07.classImage_singleton
#print axioms ErdosMahlerAudit.Gate07.classImage_singleton

-- Growth.lean
#check @ErdosMahlerAudit.Gate07.dilate_sub
#print axioms ErdosMahlerAudit.Gate07.dilate_sub
#check @ErdosMahlerAudit.Gate07.dilate_mul
#print axioms ErdosMahlerAudit.Gate07.dilate_mul
#check @ErdosMahlerAudit.Gate07.sub_card_swap
#print axioms ErdosMahlerAudit.Gate07.sub_card_swap
#check @ErdosMahlerAudit.Gate07.triple_sub_bound
#print axioms ErdosMahlerAudit.Gate07.triple_sub_bound
#check @ErdosMahlerAudit.Gate07.first_dilate_bound
#print axioms ErdosMahlerAudit.Gate07.first_dilate_bound
#check @ErdosMahlerAudit.Gate07.triangle_dilate_step
#print axioms ErdosMahlerAudit.Gate07.triangle_dilate_step
#check @ErdosMahlerAudit.Gate07.iterated_dilate_bound
#print axioms ErdosMahlerAudit.Gate07.iterated_dilate_bound
#check @ErdosMahlerAudit.Gate07.power_class_bound
#print axioms ErdosMahlerAudit.Gate07.power_class_bound

-- PositiveRationals.lean
#check @ErdosMahlerAudit.Gate07.PositiveRat
#print axioms ErdosMahlerAudit.Gate07.PositiveRat
#print ErdosMahlerAudit.Gate07.PositiveRat
#check @ErdosMahlerAudit.Gate07.PositiveRatAdd
#print axioms ErdosMahlerAudit.Gate07.PositiveRatAdd
#print ErdosMahlerAudit.Gate07.PositiveRatAdd
#check @ErdosMahlerAudit.Gate07.positiveValue
#print axioms ErdosMahlerAudit.Gate07.positiveValue
#print ErdosMahlerAudit.Gate07.positiveValue
#check @ErdosMahlerAudit.Gate07.positiveValue_injective
#print axioms ErdosMahlerAudit.Gate07.positiveValue_injective
#check @ErdosMahlerAudit.Gate07.positiveValue_pos
#print axioms ErdosMahlerAudit.Gate07.positiveValue_pos
#check @ErdosMahlerAudit.Gate07.positiveValue_add
#print axioms ErdosMahlerAudit.Gate07.positiveValue_add
#check @ErdosMahlerAudit.Gate07.positiveValue_sub
#print axioms ErdosMahlerAudit.Gate07.positiveValue_sub
#check @ErdosMahlerAudit.Gate07.positiveValue_nsmul
#print axioms ErdosMahlerAudit.Gate07.positiveValue_nsmul
#check @ErdosMahlerAudit.Gate07.positiveRatAdd_torsionFree
#print axioms ErdosMahlerAudit.Gate07.positiveRatAdd_torsionFree
#check @ErdosMahlerAudit.Gate07.positive_class_eq_iff
#print axioms ErdosMahlerAudit.Gate07.positive_class_eq_iff
#check @ErdosMahlerAudit.Gate07.rational_power_class_eq_iff
#print axioms ErdosMahlerAudit.Gate07.rational_power_class_eq_iff
#check @ErdosMahlerAudit.Gate07.selectedPositive
#print axioms ErdosMahlerAudit.Gate07.selectedPositive
#print ErdosMahlerAudit.Gate07.selectedPositive
#check @ErdosMahlerAudit.Gate07.selectedPositive_value_image
#print axioms ErdosMahlerAudit.Gate07.selectedPositive_value_image
#check @ErdosMahlerAudit.Gate07.selectedPositive_card
#print axioms ErdosMahlerAudit.Gate07.selectedPositive_card
#check @ErdosMahlerAudit.Gate07.selectedPositive_sum_image
#print axioms ErdosMahlerAudit.Gate07.selectedPositive_sum_image
#check @ErdosMahlerAudit.Gate07.selectedPositive_sum_card
#print axioms ErdosMahlerAudit.Gate07.selectedPositive_sum_card
#check @ErdosMahlerAudit.Gate07.selectedClasses
#print axioms ErdosMahlerAudit.Gate07.selectedClasses
#print ErdosMahlerAudit.Gate07.selectedClasses
#check @ErdosMahlerAudit.Gate07.mem_selectedClasses
#print axioms ErdosMahlerAudit.Gate07.mem_selectedClasses
#check @ErdosMahlerAudit.Gate07.selectedClasses_empty
#print axioms ErdosMahlerAudit.Gate07.selectedClasses_empty
#check @ErdosMahlerAudit.Gate07.selected_fractions_power_class_bounds
#print axioms ErdosMahlerAudit.Gate07.selected_fractions_power_class_bounds
#check @ErdosMahlerAudit.Gate07.selected_fractions_power_class_bound
#print axioms ErdosMahlerAudit.Gate07.selected_fractions_power_class_bound

-- Final theorem types, with all ordinary parameters visible.
set_option pp.explicit true in
#check @ErdosMahlerAudit.Gate07.power_class_bound
set_option pp.explicit true in
#check @ErdosMahlerAudit.Gate07.selected_fractions_power_class_bound
#print ErdosMahlerAudit.Gate07.power_class_bound
#print ErdosMahlerAudit.Gate07.selected_fractions_power_class_bound

open ErdosMahlerAudit ErdosMahlerAudit.Gate07
open scoped Pointwise

-- k=1 and singleton: both the class count and the doubling constant are exactly one.
#check power_class_bound ({0} : Finset ℤ) (by simp) 1 (by decide)
#check (show ((classImage 2 ({0} : Finset ℤ)).card : ℝ) = 1 from by
  rw [classImage_singleton]; norm_num)
#check (show ((({0} : Finset ℤ) + {0}).card : ℝ) / ({0} : Finset ℤ).card = 1 from by simp)

-- The quotient does not collapse distinct integer classes modulo 2.
#check (show classMap 2 (0 : ℤ) ≠ classMap 2 1 from by
  intro h
  obtain ⟨g, hg⟩ := (class_eq_iff 2 (0 : ℤ) 1).mp h
  simp only [sub_eq_add_neg, zero_add, nsmul_eq_mul] at hg
  omega)

-- Actual rational power relation: 4/1=2^2, with a positive rational root.
#check (show classMap 2 (Additive.ofMul (⟨4, by norm_num⟩ : PositiveRat)) =
    classMap 2 (Additive.ofMul (⟨1, by norm_num⟩ : PositiveRat)) from by
  apply (rational_power_class_eq_iff 2 4 1 (by norm_num) (by norm_num)).mpr
  exact ⟨2, by norm_num, by norm_num⟩)

-- Empty actual Gate 06 block; no quotient of cardinalities is used.
#check (show selectedClasses 0 5 (9 / 8) 1 2 = ∅ from
  selectedClasses_empty (Gate06.selected_sets_empty (by simp [Gate06.exceptionalBand])).1 2)
#check classImage_empty (G := ℤ) 2
#check translated_dilate_card (G := ℤ) 2 (by decide) 1 (∅ : Finset ℤ)
#check triangle_dilate_step (∅ : Finset ℤ) 2 (by decide)

-- Positive rationals also have genuinely distinct classes: 2/1 is not a rational square.
#check (show classMap 2 (Additive.ofMul (⟨2, by norm_num⟩ : PositiveRat)) ≠
    classMap 2 (Additive.ofMul (⟨1, by norm_num⟩ : PositiveRat)) from by
  intro h
  obtain ⟨g, _, hg⟩ := (rational_power_class_eq_iff 2 2 1 (by norm_num) (by norm_num)).mp h
  have hs : IsSquare (2 : ℚ) := ⟨g, by simpa only [div_one, pow_two] using hg⟩
  exact Nat.prime_two.not_isSquare (Rat.isSquare_natCast_iff.mp hs))
