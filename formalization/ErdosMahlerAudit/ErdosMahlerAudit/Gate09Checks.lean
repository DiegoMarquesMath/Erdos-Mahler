module

import all ErdosMahlerAudit.Gate09.Counting
import all ErdosMahlerAudit.Gate09.Decay
import all ErdosMahlerAudit.Gate09.DenominatorRange
public import ErdosMahlerAudit.Gate09.DenominatorRange
public import Lean

/-! Gate 09: ordinary hypotheses, foundational dependencies, and boundary checks. -/

set_option format.width 110
set_option pp.proofs false

#check @ErdosMahlerAudit.Gate09.selected_fraction_fiber_sum
#print axioms ErdosMahlerAudit.Gate09.selected_fraction_fiber_sum
#check @ErdosMahlerAudit.Gate09.selected_card_le_class_card
#print axioms ErdosMahlerAudit.Gate09.selected_card_le_class_card
#check @ErdosMahlerAudit.Gate09.rigidityThreshold_ge_four
#print axioms ErdosMahlerAudit.Gate09.rigidityThreshold_ge_four
#check @ErdosMahlerAudit.Gate09.class_count_and_size_bound
#print axioms ErdosMahlerAudit.Gate09.class_count_and_size_bound
#check @ErdosMahlerAudit.Gate09.exceptional_band_card_zero_of_selected_card_zero
#print axioms ErdosMahlerAudit.Gate09.exceptional_band_card_zero_of_selected_card_zero
#check @ErdosMahlerAudit.Gate09.inverse_ratio_exp
#print axioms ErdosMahlerAudit.Gate09.inverse_ratio_exp
#check @ErdosMahlerAudit.Gate09.normalized_power_bound
#print axioms ErdosMahlerAudit.Gate09.normalized_power_bound
#check @ErdosMahlerAudit.Gate09.coefficient_absorption
#print axioms ErdosMahlerAudit.Gate09.coefficient_absorption
#check @ErdosMahlerAudit.Gate09.least_exponent_log_denominator
#print axioms ErdosMahlerAudit.Gate09.least_exponent_log_denominator
#check @ErdosMahlerAudit.Gate09.root_exp_bound
#print axioms ErdosMahlerAudit.Gate09.root_exp_bound
#check @ErdosMahlerAudit.Gate09.uniform_exp_bound
#print axioms ErdosMahlerAudit.Gate09.uniform_exp_bound
#check @ErdosMahlerAudit.Gate09.denominator_range_at_threshold
#print axioms ErdosMahlerAudit.Gate09.denominator_range_at_threshold
#check @ErdosMahlerAudit.Gate09.denominator_range_bound
#print axioms ErdosMahlerAudit.Gate09.denominator_range_bound

-- Materialize every object that determines the meaning of the conclusion.
#print ErdosMahlerAudit.Exceptional
#print ErdosMahlerAudit.convergentDenominators
#print ErdosMahlerAudit.Gate06.V
#print ErdosMahlerAudit.Gate06.H
#print ErdosMahlerAudit.Gate06.exceptionalBand
#print ErdosMahlerAudit.Gate06.selectedFraction
#print ErdosMahlerAudit.Gate06.selectedFractions
#print ErdosMahlerAudit.Gate07.selectedPositive
#print ErdosMahlerAudit.Gate07.multipleSubgroup
#print ErdosMahlerAudit.Gate07.classMap
#print ErdosMahlerAudit.Gate07.classImage
#print ErdosMahlerAudit.Gate07.selectedClasses
#print ErdosMahlerAudit.Gate08.selectedFiber
#print ErdosMahlerAudit.Gate08.leastExponent
#print ErdosMahlerAudit.Gate08.leastPower
#print ErdosMahlerAudit.Gate08.rationalHeight
#print ErdosMahlerAudit.Gate08.MatveevRationalThree
#print ErdosMahlerAudit.Gate08.matveevConstant
#print ErdosMahlerAudit.Gate08.rigidityThreshold

-- Exact library inputs and prior interfaces used in this gate.
#check @Finset.card_eq_sum_card_image
#check @Real.exp_log
#check @Real.log_pow
#check @Real.log_le_log
#check @Real.one_sub_inv_le_log_of_pos
#check @Real.log_le_sub_one_of_pos
#check @Real.two_mul_le_exp
#check @Real.log_le_iff_le_exp
#check @Real.exp_le_exp
#check @ErdosMahlerAudit.Gate07.selectedPositive_card
#check @ErdosMahlerAudit.Gate07.selected_fractions_power_class_bound
#check @ErdosMahlerAudit.Gate08.selectedFiber_card_at_threshold
#check @ErdosMahlerAudit.Gate08.leastExponent_pos
#check @ErdosMahlerAudit.Gate08.leastExponent_log_bound
#check @ErdosMahlerAudit.Gate06.exceptional_band_multiplicity

open ErdosMahlerAudit ErdosMahlerAudit.Gate09 ErdosMahlerAudit.Gate08

-- The empty implication is checked on the full manuscript domain.
#check @exceptional_band_card_zero_of_selected_card_zero
#check selected_fraction_fiber_sum 0 5 (9 / 8) 1 4
#check (show (Gate06.selectedFractions 0 5 (9 / 8) 1).card = 0 from by
  simp [Gate06.selectedFractions, Gate06.exceptionalBand])

-- k=1 occurs below the large-x domain; x=2 has exactly k=2 and q=4.
#check (show leastExponent (4 / 3) = 1 from by
  apply le_antisymm
  · by_contra h
    have hm := leastExponent_min (x := 4 / 3) (j := 1) (by omega)
    norm_num at hm
  · have hm := leastExponent_spec (4 / 3)
    by_contra h
    have he : leastExponent (4 / 3) = 0 := by omega
    rw [he] at hm
    norm_num at hm)
#check (show leastExponent 2 = 2 from by
  apply le_antisymm
  · by_contra h
    have hm := leastExponent_min (x := 2) (j := 2) (by omega)
    norm_num at hm
  · have hm := leastExponent_spec 2
    by_contra h
    have he : leastExponent 2 = 0 ∨ leastExponent 2 = 1 := by omega
    rcases he with he | he <;> rw [he] at hm <;> norm_num at hm)
#check leastExponent_pos (x := 2) (by norm_num)
#check leastPower_bounds (x := 2) (by norm_num)
#check @normalized_power_bound (k := 1)
#check coefficient_absorption (x := 4) (by norm_num)
#check least_exponent_log_denominator (x := 2) (by norm_num)

-- N=1 is an actual convergent denominator, excluded solely by the x cutoff.
#check Gate03.one_mem_convergentDenominators
#check (show ∀ w : ℝ, 1 ≤ w → ¬ (4 ≤ Real.log ((1 : ℝ) / w)) from by
  intro w hw hx
  have hw0 : 0 < w := by linarith
  have hl := Real.log_nonpos (by positivity : 0 ≤ (1 : ℝ) / w)
    ((div_le_one₀ hw0).mpr hw)
  linarith)
#check (show ∀ N : ℝ, 0 < N → (1 : ℝ) / N = Real.exp (-Real.log N) from by
  intro N hN
  simpa using inverse_ratio_exp hN (by norm_num : (0 : ℝ) < 1))

-- Read the stored elaborated terms, including ordinary parameters.
open Lean Elab Command in
run_elab do
  let names := #[
    ``ErdosMahlerAudit.Gate09.selected_fraction_fiber_sum,
    ``ErdosMahlerAudit.Gate09.selected_card_le_class_card,
    ``ErdosMahlerAudit.Gate09.rigidityThreshold_ge_four,
    ``ErdosMahlerAudit.Gate09.class_count_and_size_bound,
    ``ErdosMahlerAudit.Gate09.exceptional_band_card_zero_of_selected_card_zero,
    ``ErdosMahlerAudit.Gate09.inverse_ratio_exp,
    ``ErdosMahlerAudit.Gate09.normalized_power_bound,
    ``ErdosMahlerAudit.Gate09.coefficient_absorption,
    ``ErdosMahlerAudit.Gate09.least_exponent_log_denominator,
    ``ErdosMahlerAudit.Gate09.root_exp_bound,
    ``ErdosMahlerAudit.Gate09.uniform_exp_bound,
    ``ErdosMahlerAudit.Gate09.denominator_range_at_threshold,
    ``ErdosMahlerAudit.Gate09.denominator_range_bound
  ]
  for n in names do
    let ci ← getConstInfo n
    logInfo m!"DECL {n}"
    logInfo m!"TYPE {ci.type}"
    let some v := ci.value? true | throwError "Proof term unavailable for {n}"
    let deps := v.getUsedConstants
    logInfo m!"DIRECT_VALUE_CONSTANT_COUNT {deps.size}"
    logInfo m!"DIRECT_PROJECT_DEPENDENCIES {deps.filter fun d =>
      d.toString.startsWith "ErdosMahlerAudit."}"
    let axs ← Lean.collectAxioms n
    logInfo m!"AXIOMS {axs}"
    for a in axs do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "Unexpected foundational dependency {a} in {n}"
