module

import all ErdosMahlerAudit.Basic
import all ErdosMahlerAudit.Definitions
import all ErdosMahlerAudit.Gate02.AdmissibleChoices
import all ErdosMahlerAudit.Gate02.Density
import all ErdosMahlerAudit.Gate02.Exceptional
import all ErdosMahlerAudit.Gate02.FiniteCounting
import all ErdosMahlerAudit.Gate03.Approximation
import all ErdosMahlerAudit.Gate03.Denominators
import all ErdosMahlerAudit.Gate03.Rotation
import all ErdosMahlerAudit.Gate03.Successors
import all ErdosMahlerAudit.Gate04.DyadicDecomposition
import all ErdosMahlerAudit.Gate04.Neighborhood
import all ErdosMahlerAudit.Gate04.RationalGrid
import all ErdosMahlerAudit.Gate04.ShellCounting
import all ErdosMahlerAudit.Gate04.SmallDenominators
import all ErdosMahlerAudit.Gate04.TruncatedCounting
import all ErdosMahlerAudit.Gate05.Arithmetic
import all ErdosMahlerAudit.Gate05.EscapingDenominators
import all ErdosMahlerAudit.Gate05.ExternalContract
import all ErdosMahlerAudit.Gate05.FinitePairs
import all ErdosMahlerAudit.Gate05.HeightBound
import all ErdosMahlerAudit.Gate05.HeightEstimates
import all ErdosMahlerAudit.Gate05.LocalProduct
import all ErdosMahlerAudit.Gate05.LogarithmicHeight
import all ErdosMahlerAudit.Gate05.SmoothPart
import all ErdosMahlerAudit.Gate06.Band
import all ErdosMahlerAudit.Gate06.Multiplicity
import all ErdosMahlerAudit.Gate06.PrescribedProducts
import all ErdosMahlerAudit.Gate06.ProductError
import all ErdosMahlerAudit.Gate06.ProductTransfer
import all ErdosMahlerAudit.Gate06.Separation
import all ErdosMahlerAudit.Gate07.Classes
import all ErdosMahlerAudit.Gate07.Growth
import all ErdosMahlerAudit.Gate07.PositiveRationals
import all ErdosMahlerAudit.Gate08.Counting
import all ErdosMahlerAudit.Gate08.Height
import all ErdosMahlerAudit.Gate08.LogError
import all ErdosMahlerAudit.Gate08.PowerSize
import all ErdosMahlerAudit.Gate08.Rigidity
import all ErdosMahlerAudit.Gate08.Selection
import all ErdosMahlerAudit.Gate08.Valuation
import all ErdosMahlerAudit.Gate08.Weighted
import all ErdosMahlerAudit.Gate09.Counting
import all ErdosMahlerAudit.Gate09.Decay
import all ErdosMahlerAudit.Gate09.DenominatorRange
import all ErdosMahlerAudit.Gate10.Bands
import all ErdosMahlerAudit.Gate10.Proposition
import all ErdosMahlerAudit.Gate10.Scales
import all ErdosMahlerAudit.Gate10.Series
import all ErdosMahlerAudit.Gate10.Successors
import all ErdosMahlerAudit.Gate10.Summation
import all ErdosMahlerAudit.Gate11.Intervals
import all ErdosMahlerAudit.Gate11.Separation
import all ErdosMahlerAudit.Gate11.Successors
import all ErdosMahlerAudit.RationalArithmetic
import all ErdosMahlerAudit.Gate13.Prefix
import all ErdosMahlerAudit.Gate13.Limits
import all ErdosMahlerAudit.Gate13.Topology
import all ErdosMahlerAudit.Gate12.Tree
import all ErdosMahlerAudit.Gate12.Selection
import all ErdosMahlerAudit.Gate14.Arithmetic
import all ErdosMahlerAudit.Gate14.Convergents
import all ErdosMahlerAudit.Gate14.Irrationality
import all ErdosMahlerAudit.Gate14.LowerExponent
import all ErdosMahlerAudit.Gate14.Theorem
import all Mathlib.NumberTheory.DiophantineApproximation.Basic
import all Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions
import all ErdosMahlerAudit.Gate15.Partition
import all ErdosMahlerAudit.Gate15.Bands
import all ErdosMahlerAudit.Gate15.Asymptotic
import all ErdosMahlerAudit.Gate15.FiniteApproximants
import all ErdosMahlerAudit.Gate15.Theorem
public import ErdosMahlerAudit.Gate15.Theorem
public import Lean

/-! Complete interfaces, boundary specializations, and independent stored-body audits. -/

set_option format.width 110
set_option pp.fullNames true
set_option pp.funBinderTypes true

#check @ErdosMahlerAudit.Gate15.nat_partition
#print axioms ErdosMahlerAudit.Gate15.nat_partition

#check @ErdosMahlerAudit.Gate15.denominator_partition
#print axioms ErdosMahlerAudit.Gate15.denominator_partition

#check @ErdosMahlerAudit.Gate15.partition_endpoint
#print axioms ErdosMahlerAudit.Gate15.partition_endpoint

#check @ErdosMahlerAudit.Gate15.band_index_ge
#print axioms ErdosMahlerAudit.Gate15.band_index_ge

#check @ErdosMahlerAudit.Gate15.prescribed_case
#print axioms ErdosMahlerAudit.Gate15.prescribed_case

#check @ErdosMahlerAudit.Gate15.cutoff_error
#print axioms ErdosMahlerAudit.Gate15.cutoff_error

#check @ErdosMahlerAudit.Gate15.next_cutoff
#print axioms ErdosMahlerAudit.Gate15.next_cutoff

#check @ErdosMahlerAudit.Gate15.cutoff_error_strict
#print axioms ErdosMahlerAudit.Gate15.cutoff_error_strict

#check @ErdosMahlerAudit.Gate15.quadratic_to_band
#print axioms ErdosMahlerAudit.Gate15.quadratic_to_band

#check @ErdosMahlerAudit.Gate15.actual_successor_admissible
#print axioms ErdosMahlerAudit.Gate15.actual_successor_admissible

#check @ErdosMahlerAudit.Gate15.cutoff_identity
#print axioms ErdosMahlerAudit.Gate15.cutoff_identity

#check @ErdosMahlerAudit.Gate15.small_case
#print axioms ErdosMahlerAudit.Gate15.small_case

#check @ErdosMahlerAudit.Gate15.not_next
#print axioms ErdosMahlerAudit.Gate15.not_next

#check @ErdosMahlerAudit.Gate15.next_error
#print axioms ErdosMahlerAudit.Gate15.next_error

#check @ErdosMahlerAudit.Gate15.large_case
#print axioms ErdosMahlerAudit.Gate15.large_case

#check @ErdosMahlerAudit.Gate15.nonprescribed_band
#print axioms ErdosMahlerAudit.Gate15.nonprescribed_band

#check @ErdosMahlerAudit.Gate15.finite_band
#print axioms ErdosMahlerAudit.Gate15.finite_band

#check @ErdosMahlerAudit.Gate15.index_tendsto
#print axioms ErdosMahlerAudit.Gate15.index_tendsto

#check @ErdosMahlerAudit.Gate15.nu_tendsto
#print axioms ErdosMahlerAudit.Gate15.nu_tendsto

#check @ErdosMahlerAudit.Gate15.nu_eventually
#print axioms ErdosMahlerAudit.Gate15.nu_eventually

#check @ErdosMahlerAudit.Gate15.power_eventually
#print axioms ErdosMahlerAudit.Gate15.power_eventually

#check @ErdosMahlerAudit.Gate15.absorb_band_constant
#print axioms ErdosMahlerAudit.Gate15.absorb_band_constant

#check @ErdosMahlerAudit.Gate15.high_denominator_in_interval
#print axioms ErdosMahlerAudit.Gate15.high_denominator_in_interval

#check @ErdosMahlerAudit.Gate15.outside_margin
#print axioms ErdosMahlerAudit.Gate15.outside_margin

#check @ErdosMahlerAudit.Gate15.all_rational_high_denominator
#print axioms ErdosMahlerAudit.Gate15.all_rational_high_denominator

#check @ErdosMahlerAudit.Gate15.finite_bounded_denominator_near
#print axioms ErdosMahlerAudit.Gate15.finite_bounded_denominator_near

#check @ErdosMahlerAudit.Gate15.finite_of_high_denominator
#print axioms ErdosMahlerAudit.Gate15.finite_of_high_denominator

#check @ErdosMahlerAudit.Gate15.upper_from_arithmetic
#print axioms ErdosMahlerAudit.Gate15.upper_from_arithmetic

#check @ErdosMahlerAudit.Gate15.upper_irrationality_exponent
#print axioms ErdosMahlerAudit.Gate15.upper_irrationality_exponent

#check @ErdosMahlerAudit.Gate15.UpperSpec
#print axioms ErdosMahlerAudit.Gate15.UpperSpec
#check @ErdosMahlerAudit.Gate15.UpperSpec.high_denominator
#print axioms ErdosMahlerAudit.Gate15.UpperSpec.high_denominator
#check @ErdosMahlerAudit.Gate15.UpperSpec.finite_too_good
#print axioms ErdosMahlerAudit.Gate15.UpperSpec.finite_too_good

#print ErdosMahlerAudit.Gate15.UpperSpec
#print ErdosMahlerAudit.Gate15.upper_irrationality_exponent
#print ErdosMahlerAudit.Gate05.SubspaceTwoThreePrimitive
#print ErdosMahlerAudit.Gate08.MatveevRationalThree
#print ErdosMahlerAudit.Gate02.cutoff
#print ErdosMahlerAudit.Gate02.nu

-- Exact public signature: no certificate or auxiliary mathematical premise is an input.
open ErdosMahlerAudit in
#check (show Gate05.SubspaceTwoThreePrimitive → Gate08.MatveevRationalThree →
    ∀ τ : ℝ, 4 ≤ τ →
    ∃ (K : Set ℝ) (ξ : (ℕ → Bool) → ℝ) (t0 : ℕ) (f : List Bool → ℕ),
      Gate13.CantorSpec τ t0 f ξ K ∧ Gate14.ArithmeticLowerSpec τ t0 f ξ ∧
        Gate15.UpperSpec τ t0 f ξ from @Gate15.upper_irrationality_exponent)

-- τ=4; j=0; v=Q_j, including the band endpoint.
open ErdosMahlerAudit in
#check fun hST hM => Gate15.upper_irrationality_exponent hST hM 4 (by norm_num)
open ErdosMahlerAudit in
#check fun {τ t0 f ξ} (hA : Gate14.ArithmeticLowerSpec τ t0 f ξ) ε =>
  Gate15.denominator_partition hA ε (v := Gate14.Q f ε 0) le_rfl
open ErdosMahlerAudit in
#check fun {τ t0 f ξ} (hA : Gate14.ArithmeticLowerSpec τ t0 f ξ) ε j =>
  (Gate15.partition_endpoint hA ε j j).2 rfl
open ErdosMahlerAudit in
#check fun {τ t0 f ξ} (hA : Gate14.ArithmeticLowerSpec τ t0 f ξ) ε j =>
  Gate15.prescribed_case hA ε j (q := Gate14.r f ε j) rfl

-- Equality at the real cutoff belongs to the small case; strict sides are separate.
open ErdosMahlerAudit in
#check fun {τ t0 f ξ} (hA : Gate14.ArithmeticLowerSpec τ t0 f ξ) ε j q
    (hne : q ≠ Gate14.r f ε j) (hb : Gate14.Q f ε j ≤ q.den)
    (hc : (q.den : ℝ) = Gate02.cutoff (Gate14.t f ε j) τ) =>
  Gate15.small_case hA ε j q hne hb hc.le
open ErdosMahlerAudit in
#check fun {τ t0 f ξ} (hA : Gate14.ArithmeticLowerSpec τ t0 f ξ) ε j q
    (hne : q ≠ Gate14.r f ε j) (hb : Gate14.Q f ε j ≤ q.den)
    (hc : (q.den : ℝ) < Gate02.cutoff (Gate14.t f ε j) τ) =>
  Gate15.small_case hA ε j q hne hb hc.le
#check @ErdosMahlerAudit.Gate15.large_case
#check @ErdosMahlerAudit.Gate15.not_next
open ErdosMahlerAudit in
#check Gate15.next_cutoff (S := 3) (v := 2) (τ := 4) (by norm_num) (by norm_num) (by norm_num)

-- Every real s>τ, including arbitrary closeness from above.
open ErdosMahlerAudit in
#check fun {τ t0 f ξ} (hU : Gate15.UpperSpec τ t0 f ξ) ε (η : ℝ) (hη : 0 < η) =>
  hU.finite_too_good ε (τ + η) (by linarith)
#check @ErdosMahlerAudit.Gate15.nu_tendsto

-- Signed rational numerators and denominator one are included in the finite grid.
#check ErdosMahlerAudit.Gate15.finite_bounded_denominator_near (3 / 2) 2
open ErdosMahlerAudit in
#check fun (x : ℝ) (h1 : 1 < x) (h2 : x < 2) =>
  Gate15.outside_margin h1 h2 (-1) (by norm_num)
open ErdosMahlerAudit in
#check fun (x : ℝ) (h1 : 1 < x) (h2 : x < 2) =>
  Gate15.outside_margin h1 h2 3 (by norm_num)

-- Inspection of kernel environment data, independent of #print axioms.
-- The finite audit traverses several hundred inherited declarations.
set_option maxHeartbeats 4000000 in
-- Traverse and collect axioms for every inherited project body as well as the new declarations.
open Lean Elab Command in
run_elab do
  let env ← getEnv
  let mut count : Nat := 0
  let mut bodyCount : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "ErdosMahlerAudit.Gate15." ||
        n.toString.startsWith "_private.ErdosMahlerAudit.Gate15." then
      let ci ← getConstInfo n
      count := count + 1
      logInfo m!"DECL {n}\nTYPE {ci.type}"
      if ci.isUnsafe || ci.isPartial then throwError "Unsafe or partial declaration {n}"
      match ci with
      | .axiomInfo _ => throwError "Unexpected new axiom {n}"
      | .opaqueInfo _ => throwError "Unexpected opaque declaration {n}"
      | _ => pure ()
      if let some v := ci.value? true then
        bodyCount := bodyCount + 1
        let deps := ci.type.getUsedConstants ++ v.getUsedConstants
        logInfo m!"STORED_BODY_PRESENT {n}\nDIRECT_DEPENDENCIES {deps}"
      else
        match ci with
        | .defnInfo _ | .thmInfo _ => throwError "Missing stored body {n}"
        | _ => pure ()
      let axs ← Lean.collectAxioms n
      logInfo m!"INDEPENDENT_AXIOMS {n}: {axs}"
      for a in axs do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
          throwError "Unexpected dependency {a} in {n}"
  logInfo m!"ALL_GATE15_DECLARATIONS_AUDITED {count}; STORED_BODIES {bodyCount}"
  let edges := #[
    (``ErdosMahlerAudit.Gate15.upper_irrationality_exponent,
      ``ErdosMahlerAudit.Gate14.prescribed_convergents_lower_exponent),
    (``ErdosMahlerAudit.Gate15.upper_irrationality_exponent,
      ``ErdosMahlerAudit.Gate15.upper_from_arithmetic),
    (``ErdosMahlerAudit.Gate15.actual_successor_admissible,
      ``ErdosMahlerAudit.Gate12.PairSpec.admissible),
    (``ErdosMahlerAudit.Gate15.actual_successor_admissible,
      ``ErdosMahlerAudit.Gate12.TreeSpec.pairs),
    (``ErdosMahlerAudit.Gate15.large_case,
      ``ErdosMahlerAudit.Gate15.actual_successor_admissible),
    (``ErdosMahlerAudit.Gate15.large_case,
      ``ErdosMahlerAudit.Gate02.admissible_approximation_lower),
    (``ErdosMahlerAudit.Gate15.large_case, ``ErdosMahlerAudit.rational_separation),
    (``ErdosMahlerAudit.Gate15.small_case, ``ErdosMahlerAudit.rational_separation),
    (``ErdosMahlerAudit.Gate15.denominator_partition,
      ``ErdosMahlerAudit.Gate14.ArithmeticLowerSpec.denominator_tendsto),
    (``ErdosMahlerAudit.Gate15.finite_of_high_denominator,
      ``ErdosMahlerAudit.Gate15.finite_bounded_denominator_near)
  ]
  for (src, dst) in edges do
    let ci ← getConstInfo src
    let some v := ci.value? true | throwError "Missing stored body {src}"
    unless v.getUsedConstants.contains dst do
      throwError "Missing stored edge {src} -> {dst}"
    logInfo m!"VERIFIED_STORED_EDGE {src} -> {dst}"
  let mut pending := #[``ErdosMahlerAudit.Gate15.upper_irrationality_exponent]
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      let ci ← getConstInfo n
      if ci.isUnsafe || ci.isPartial then throwError "Unsafe or partial inherited declaration {n}"
      match ci with
      | .axiomInfo _ => throwError "Project axiom on dependency path {n}"
      | .opaqueInfo _ => throwError "Opaque project body on dependency path {n}"
      | _ => pure ()
      let mut deps := ci.type.getUsedConstants
      if let some v := ci.value? true then
        deps := deps ++ v.getUsedConstants
        logInfo m!"TRANSITIVE_STORED_BODY {n}"
      else
        match ci with
        | .defnInfo _ | .thmInfo _ => throwError "Missing inherited body {n}"
        | _ => pure ()
      let axs ← Lean.collectAxioms n
      for a in axs do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
          throwError "Unapproved inherited dependency {a} in {n}"
      logInfo m!"TRANSITIVE_AXIOMS {n}: {axs}"
      for d in deps do
        if d.toString.startsWith "ErdosMahlerAudit." ||
            d.toString.startsWith "_private.ErdosMahlerAudit." then
          pending := pending.push d
  for n in #[``ErdosMahlerAudit.Gate14.prescribed_convergents_lower_exponent,
      ``ErdosMahlerAudit.Gate13.cantor_set_of_tau,
      ``ErdosMahlerAudit.Gate15.actual_successor_admissible,
      ``ErdosMahlerAudit.Gate12.PairSpec.admissible,
      ``ErdosMahlerAudit.Gate02.admissible_approximation_lower,
      ``ErdosMahlerAudit.Gate15.denominator_partition,
      ``ErdosMahlerAudit.Gate15.nu_tendsto,
      ``ErdosMahlerAudit.Gate15.all_rational_high_denominator,
      ``ErdosMahlerAudit.Gate15.finite_bounded_denominator_near,
      ``ErdosMahlerAudit.rational_separation, ``ErdosMahlerAudit.R_den] do
    unless seen.contains n do throwError "Missing public dependency path to {n}"
    logInfo m!"VERIFIED_PUBLIC_PATH {n}"
  logInfo m!"TRANSITIVE_PROJECT_DECLARATIONS_AUDITED {seen.size}"
