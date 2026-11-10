module

import all ErdosMahlerAudit.Gate10.Series
import all ErdosMahlerAudit.Gate10.Scales
import all ErdosMahlerAudit.Gate10.Bands
import all ErdosMahlerAudit.Gate10.Summation
import all ErdosMahlerAudit.Gate10.Proposition
import all ErdosMahlerAudit.Gate10.Successors
public import ErdosMahlerAudit.Gate10.Successors
public import Lean

/-! Gate10 exact types, stored proof dependencies, and boundary checks. -/

set_option format.width 110

-- Series.lean
#check @ErdosMahlerAudit.Gate10.bandMajorant
#print axioms ErdosMahlerAudit.Gate10.bandMajorant
#check @ErdosMahlerAudit.Gate10.bandMajorant_pos
#print axioms ErdosMahlerAudit.Gate10.bandMajorant_pos
#check @ErdosMahlerAudit.Gate10.bandMajorant_eventually_le
#print axioms ErdosMahlerAudit.Gate10.bandMajorant_eventually_le
#check @ErdosMahlerAudit.Gate10.bandMajorant_summable
#print axioms ErdosMahlerAudit.Gate10.bandMajorant_summable
#check @ErdosMahlerAudit.Gate10.bandMajorant_finite_tail
#print axioms ErdosMahlerAudit.Gate10.bandMajorant_finite_tail

-- Scales.lean
#check @ErdosMahlerAudit.Gate10.chosenTheta
#print axioms ErdosMahlerAudit.Gate10.chosenTheta
#check @ErdosMahlerAudit.Gate10.chosenTheta_admissible
#print axioms ErdosMahlerAudit.Gate10.chosenTheta_admissible
#check @ErdosMahlerAudit.Gate10.heightScale
#print axioms ErdosMahlerAudit.Gate10.heightScale
#check @ErdosMahlerAudit.Gate10.heightScale_eq_rpow
#print axioms ErdosMahlerAudit.Gate10.heightScale_eq_rpow
#check @ErdosMahlerAudit.Gate10.heightScale_zero
#print axioms ErdosMahlerAudit.Gate10.heightScale_zero
#check @ErdosMahlerAudit.Gate10.heightScale_pos
#print axioms ErdosMahlerAudit.Gate10.heightScale_pos
#check @ErdosMahlerAudit.Gate10.heightScale_succ
#print axioms ErdosMahlerAudit.Gate10.heightScale_succ
#check @ErdosMahlerAudit.Gate10.heightScale_antitone
#print axioms ErdosMahlerAudit.Gate10.heightScale_antitone
#check @ErdosMahlerAudit.Gate10.heightScale_log_ratio
#print axioms ErdosMahlerAudit.Gate10.heightScale_log_ratio
#check @ErdosMahlerAudit.Gate10.heightScale_cover
#print axioms ErdosMahlerAudit.Gate10.heightScale_cover
#check @ErdosMahlerAudit.Gate10.heightScale_unique
#print axioms ErdosMahlerAudit.Gate10.heightScale_unique
#check @ErdosMahlerAudit.Gate10.heightScale_finite_cutoff
#print axioms ErdosMahlerAudit.Gate10.heightScale_finite_cutoff
#check @ErdosMahlerAudit.Gate10.heightScale_partition
#print axioms ErdosMahlerAudit.Gate10.heightScale_partition
#check @ErdosMahlerAudit.Gate10.heightScale_endpoint
#print axioms ErdosMahlerAudit.Gate10.heightScale_endpoint

-- Bands.lean
#check @ErdosMahlerAudit.Gate10.high_denominator_log_pos
#print axioms ErdosMahlerAudit.Gate10.high_denominator_log_pos
#check @ErdosMahlerAudit.Gate10.high_count_zero_of_height_zero
#print axioms ErdosMahlerAudit.Gate10.high_count_zero_of_height_zero
#check @ErdosMahlerAudit.Gate10.high_witness_covered
#print axioms ErdosMahlerAudit.Gate10.high_witness_covered
#check @ErdosMahlerAudit.Gate10.activeBand_bounds
#print axioms ErdosMahlerAudit.Gate10.activeBand_bounds
#check @ErdosMahlerAudit.Gate10.eventually_height_lt_N
#print axioms ErdosMahlerAudit.Gate10.eventually_height_lt_N
#check @ErdosMahlerAudit.Gate10.eventually_active_ge
#print axioms ErdosMahlerAudit.Gate10.eventually_active_ge
#check @ErdosMahlerAudit.Gate10.eventually_active_height_ge_one
#print axioms ErdosMahlerAudit.Gate10.eventually_active_height_ge_one
#check @ErdosMahlerAudit.Gate10.activeBands_finite_range
#print axioms ErdosMahlerAudit.Gate10.activeBands_finite_range
#check @ErdosMahlerAudit.Gate10.high_count_le_finite_band_sum
#print axioms ErdosMahlerAudit.Gate10.high_count_le_finite_band_sum
#check @ErdosMahlerAudit.Gate10.activeBand_height_ge_log_two
#print axioms ErdosMahlerAudit.Gate10.activeBand_height_ge_log_two
#check @ErdosMahlerAudit.Gate10.activeBands_finite_range_all
#print axioms ErdosMahlerAudit.Gate10.activeBands_finite_range_all

-- Summation.lean
#check @ErdosMahlerAudit.Gate10.band_count_le_majorant
#print axioms ErdosMahlerAudit.Gate10.band_count_le_majorant
#check @ErdosMahlerAudit.Gate10.large_denominator_negligible
#print axioms ErdosMahlerAudit.Gate10.large_denominator_negligible

-- Proposition.lean
#check @ErdosMahlerAudit.Gate10.small_remainder_identity
#print axioms ErdosMahlerAudit.Gate10.small_remainder_identity
#check @ErdosMahlerAudit.Gate10.eventually_small_remainder
#print axioms ErdosMahlerAudit.Gate10.eventually_small_remainder
#check @ErdosMahlerAudit.Gate10.proposition_2_1
#print axioms ErdosMahlerAudit.Gate10.proposition_2_1

-- Successors.lean
#check @ErdosMahlerAudit.Gate10.two_successors
#print axioms ErdosMahlerAudit.Gate10.two_successors

-- The existing objects and both full external contracts remain visible.
#print ErdosMahlerAudit.Exceptional
#print ErdosMahlerAudit.convergentDenominators
#print ErdosMahlerAudit.Gate02.E
#check @ErdosMahlerAudit.Gate02.E_eq_exceptionalCount
#print axioms ErdosMahlerAudit.Gate02.E_eq_exceptionalCount
#print ErdosMahlerAudit.Gate05.SubspaceTwoThreePrimitive
#print ErdosMahlerAudit.Gate08.MatveevRationalThree
#print ErdosMahlerAudit.Gate06.exceptionalBand
#print ErdosMahlerAudit.Gate10.bandMajorant
#print ErdosMahlerAudit.Gate10.chosenTheta
#print ErdosMahlerAudit.Gate10.heightScale

-- The pinned library signatures actually used by the new analysis.
#check @Real.isLittleO_pow_log_id_atTop
#check @Asymptotics.IsLittleO.bound
#check @Real.summable_one_div_nat_pow
#check @Summable.of_norm_bounded_eventually_nat
#check @summable_iff_vanishing_norm
#check @exists_nat_pow_near
#check @pow_unbounded_of_one_lt
#check @Finset.sum_subset
#check @Finset.card_biUnion_le
#check @Real.log_rpow
#check @tendsto_rpow_neg_atTop
#check @ErdosMahlerAudit.Gate05.logarithmicHeight_sublinear
#check @ErdosMahlerAudit.Gate09.denominator_range_at_threshold
#check @ErdosMahlerAudit.Gate04.small_denominator_estimate

open ErdosMahlerAudit ErdosMahlerAudit.Gate10

-- Exact theta at ν=5, and the arbitrary-real ν↓4 domain are both retained.
#check (show chosenTheta 5 = 9 / 8 from by norm_num [chosenTheta])
#check chosenTheta_admissible
#check heightScale_endpoint (N := 1) (θ := 9 / 8) (by norm_num) (by norm_num) 0
#check (show heightScale 8 2 2 / 2 < 2 ∧ 2 ≤ heightScale 8 2 2 from by
  norm_num [heightScale])
#check (show ¬ (heightScale 8 2 1 / 2 < 2) from by norm_num [heightScale])
#check (show ∀ θ : ℝ, bandMajorant θ 0 = 1 from by intro θ; simp [bandMajorant])
#check (show Gate06.exceptionalBand 0 5 (9 / 8) 1 = ∅ from by simp [Gate06.exceptionalBand])
#check activeBands_finite_range_all 0 5 (θ := 9 / 8) (by norm_num)
#check activeBands_finite_range_all 1 5 (θ := 9 / 8) (by norm_num)
#check (show Exceptional 5 5 1 from by
  have ha : a 5 = 8 := (exponent_unique (b := 5) (n := 8) (by norm_num)).symm
  norm_num [Exceptional, R, ha])
#check Gate05.logarithmicHeight_zero_iff
#check (show ∀ θ : ℝ, (∑ j ∈ (∅ : Finset ℕ), bandMajorant θ j) = 0 from by simp)
#check fun hST hMatveev => two_successors hST hMatveev 4 (by norm_num)

-- Inspect stored values rather than trusting reports or axiom lists alone.
open Lean Elab Command in
run_elab do
  let names := #[
    ``ErdosMahlerAudit.Gate10.bandMajorant,
    ``ErdosMahlerAudit.Gate10.bandMajorant_pos,
    ``ErdosMahlerAudit.Gate10.bandMajorant_eventually_le,
    ``ErdosMahlerAudit.Gate10.bandMajorant_summable,
    ``ErdosMahlerAudit.Gate10.bandMajorant_finite_tail,
    ``ErdosMahlerAudit.Gate10.chosenTheta,
    ``ErdosMahlerAudit.Gate10.chosenTheta_admissible,
    ``ErdosMahlerAudit.Gate10.heightScale,
    ``ErdosMahlerAudit.Gate10.heightScale_eq_rpow,
    ``ErdosMahlerAudit.Gate10.heightScale_zero,
    ``ErdosMahlerAudit.Gate10.heightScale_pos,
    ``ErdosMahlerAudit.Gate10.heightScale_succ,
    ``ErdosMahlerAudit.Gate10.heightScale_antitone,
    ``ErdosMahlerAudit.Gate10.heightScale_log_ratio,
    ``ErdosMahlerAudit.Gate10.heightScale_cover,
    ``ErdosMahlerAudit.Gate10.heightScale_unique,
    ``ErdosMahlerAudit.Gate10.heightScale_finite_cutoff,
    ``ErdosMahlerAudit.Gate10.heightScale_partition,
    ``ErdosMahlerAudit.Gate10.heightScale_endpoint,
    ``ErdosMahlerAudit.Gate10.high_denominator_log_pos,
    ``ErdosMahlerAudit.Gate10.high_count_zero_of_height_zero,
    ``ErdosMahlerAudit.Gate10.high_witness_covered,
    ``ErdosMahlerAudit.Gate10.activeBand_bounds,
    ``ErdosMahlerAudit.Gate10.eventually_height_lt_N,
    ``ErdosMahlerAudit.Gate10.eventually_active_ge,
    ``ErdosMahlerAudit.Gate10.eventually_active_height_ge_one,
    ``ErdosMahlerAudit.Gate10.activeBands_finite_range,
    ``ErdosMahlerAudit.Gate10.high_count_le_finite_band_sum,
    ``ErdosMahlerAudit.Gate10.activeBand_height_ge_log_two,
    ``ErdosMahlerAudit.Gate10.activeBands_finite_range_all,
    ``ErdosMahlerAudit.Gate10.band_count_le_majorant,
    ``ErdosMahlerAudit.Gate10.large_denominator_negligible,
    ``ErdosMahlerAudit.Gate10.small_remainder_identity,
    ``ErdosMahlerAudit.Gate10.eventually_small_remainder,
    ``ErdosMahlerAudit.Gate10.proposition_2_1,
    ``ErdosMahlerAudit.Gate10.two_successors
  ]
  for n in names do
    let ci ← getConstInfo n
    logInfo m!"DECL {n}"
    logInfo m!"TYPE {ci.type}"
    let some v := ci.value? true | throwError "Proof or definition body unavailable for {n}"
    let deps := v.getUsedConstants
    logInfo m!"DIRECT_VALUE_CONSTANT_COUNT {deps.size}"
    logInfo m!"DIRECT_PROJECT_DEPENDENCIES {deps.filter fun d =>
      d.toString.startsWith "ErdosMahlerAudit."}"
    let axs ← Lean.collectAxioms n
    logInfo m!"AXIOMS {axs}"
    for a in axs do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "Unexpected foundational dependency {a} in {n}"
