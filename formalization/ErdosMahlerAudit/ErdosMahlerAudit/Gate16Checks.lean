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
import all ErdosMahlerAudit.Gate16.Exponent
import all ErdosMahlerAudit.Gate16.Theorem
public import ErdosMahlerAudit.Gate16.Theorem
public import Lean

/-! Exact interfaces, boundary elaborations, and stored-body audit of the numeric integration. -/

set_option format.width 110
set_option pp.fullNames true
set_option pp.funBinderTypes true
set_option pp.proofs true

#check @ErdosMahlerAudit.Gate16.Good
#print axioms ErdosMahlerAudit.Gate16.Good
#check @ErdosMahlerAudit.Gate16.ApproxOrder
#print axioms ErdosMahlerAudit.Gate16.ApproxOrder
#check @ErdosMahlerAudit.Gate16.irrationalityExponent
#print axioms ErdosMahlerAudit.Gate16.irrationalityExponent
#check @ErdosMahlerAudit.Gate16.mem_good
#print axioms ErdosMahlerAudit.Gate16.mem_good
#check @ErdosMahlerAudit.Gate16.exponent_eq_sSup
#print axioms ErdosMahlerAudit.Gate16.exponent_eq_sSup
#check @ErdosMahlerAudit.Gate16.ofReal_le_exponent
#print axioms ErdosMahlerAudit.Gate16.ofReal_le_exponent
#check @ErdosMahlerAudit.Gate16.exponent_le
#print axioms ErdosMahlerAudit.Gate16.exponent_le
#check @ErdosMahlerAudit.Gate16.exponent_le_of_finite
#print axioms ErdosMahlerAudit.Gate16.exponent_le_of_finite
#check @ErdosMahlerAudit.Gate16.ofReal_le_exponent_of_infinite
#print axioms ErdosMahlerAudit.Gate16.ofReal_le_exponent_of_infinite
#check @ErdosMahlerAudit.Gate16.exponent_eq_top_of_all_orders
#print axioms ErdosMahlerAudit.Gate16.exponent_eq_top_of_all_orders
#check @ErdosMahlerAudit.Gate16.approxOrder_of_infinite_good
#print axioms ErdosMahlerAudit.Gate16.approxOrder_of_infinite_good
#check @ErdosMahlerAudit.Gate16.branch_exponent
#print axioms ErdosMahlerAudit.Gate16.branch_exponent
#check @ErdosMahlerAudit.Gate16.infinite_prescribed_convergents
#print axioms ErdosMahlerAudit.Gate16.infinite_prescribed_convergents
#check @ErdosMahlerAudit.Gate16.erdos_mahler_main
#print axioms ErdosMahlerAudit.Gate16.erdos_mahler_main
#print ErdosMahlerAudit.Gate16.Good
#print ErdosMahlerAudit.Gate16.ApproxOrder
#print ErdosMahlerAudit.Gate16.irrationalityExponent
#print ErdosMahlerAudit.Gate16.erdos_mahler_main
#check @ErdosMahlerAudit.Gate15.upper_irrationality_exponent
#print ErdosMahlerAudit.Gate15.upper_irrationality_exponent
#check @ErdosMahlerAudit.Gate15.UpperSpec
#print ErdosMahlerAudit.Gate15.UpperSpec
#check @ErdosMahlerAudit.Gate14.ArithmeticLowerSpec
#print ErdosMahlerAudit.Gate14.ArithmeticLowerSpec
#check @ErdosMahlerAudit.Gate13.CantorSpec
#print ErdosMahlerAudit.Gate13.CantorSpec
#check @ErdosMahlerAudit.Gate14.r
#print ErdosMahlerAudit.Gate14.r
#check @ErdosMahlerAudit.Gate14.Q
#print ErdosMahlerAudit.Gate14.Q
#check @ErdosMahlerAudit.Gate05.SubspaceTwoThreePrimitive
#print ErdosMahlerAudit.Gate05.SubspaceTwoThreePrimitive
#check @ErdosMahlerAudit.Gate08.MatveevRationalThree
#print ErdosMahlerAudit.Gate08.MatveevRationalThree
#check @ErdosMahlerAudit.Gate15.UpperSpec.high_denominator
#check @ErdosMahlerAudit.Gate15.UpperSpec.finite_too_good
#check @ErdosMahlerAudit.Gate14.ArithmeticLowerSpec.root
#check @ErdosMahlerAudit.Gate14.ArithmeticLowerSpec.height
#check @ErdosMahlerAudit.Gate14.ArithmeticLowerSpec.index_pos
#check @ErdosMahlerAudit.Gate14.ArithmeticLowerSpec.index_step
#check @ErdosMahlerAudit.Gate14.ArithmeticLowerSpec.denominator_pos
#check @ErdosMahlerAudit.Gate14.ArithmeticLowerSpec.denominator_three
#check @ErdosMahlerAudit.Gate14.ArithmeticLowerSpec.denominator_step
#check @ErdosMahlerAudit.Gate14.ArithmeticLowerSpec.denominator_triple
#check @ErdosMahlerAudit.Gate14.ArithmeticLowerSpec.denominator_strictMono
#check @ErdosMahlerAudit.Gate14.ArithmeticLowerSpec.denominator_tendsto
#check @ErdosMahlerAudit.Gate14.ArithmeticLowerSpec.denominator_real_tendsto
#check @ErdosMahlerAudit.Gate14.ArithmeticLowerSpec.numerator
#check @ErdosMahlerAudit.Gate14.ArithmeticLowerSpec.denominator
#check @ErdosMahlerAudit.Gate14.ArithmeticLowerSpec.reduced
#check @ErdosMahlerAudit.Gate14.ArithmeticLowerSpec.fraction
#check @ErdosMahlerAudit.Gate14.ArithmeticLowerSpec.distinct
#check @ErdosMahlerAudit.Gate14.ArithmeticLowerSpec.infinite
#check @ErdosMahlerAudit.Gate14.ArithmeticLowerSpec.displacement
#check @ErdosMahlerAudit.Gate14.ArithmeticLowerSpec.irrational
#check @ErdosMahlerAudit.Gate14.ArithmeticLowerSpec.legendre
#check @ErdosMahlerAudit.Gate14.ArithmeticLowerSpec.convergent
#check @ErdosMahlerAudit.Gate14.ArithmeticLowerSpec.convs
#check @ErdosMahlerAudit.Gate14.ArithmeticLowerSpec.eventual
#check @ErdosMahlerAudit.Gate14.ArithmeticLowerSpec.infinite_good
#check @ErdosMahlerAudit.Gate13.CantorSpec.tree
#check @ErdosMahlerAudit.Gate13.CantorSpec.range_eq
#check @ErdosMahlerAudit.Gate13.CantorSpec.nonempty
#check @ErdosMahlerAudit.Gate13.CantorSpec.subset
#check @ErdosMahlerAudit.Gate13.CantorSpec.continuous
#check @ErdosMahlerAudit.Gate13.CantorSpec.injective
#check @ErdosMahlerAudit.Gate13.CantorSpec.compact
#check @ErdosMahlerAudit.Gate13.CantorSpec.closed
#check @ErdosMahlerAudit.Gate13.CantorSpec.no_isolated
#check @ErdosMahlerAudit.Gate13.CantorSpec.homeomorph
#check @ErdosMahlerAudit.Gate13.CantorSpec.interior_empty
#check @ErdosMahlerAudit.Gate13.CantorSpec.nowhere_dense
#check @ErdosMahlerAudit.Gate13.CantorSpec.unique
#check @ErdosMahlerAudit.Gate13.CantorSpec.mem
#check @ErdosMahlerAudit.Gate13.CantorSpec.interior_mem
#check @ErdosMahlerAudit.Gate13.CantorSpec.displacement
#check @ErdosMahlerAudit.Gate13.CantorSpec.prefix_bound
#check @Rat.num
#check @Rat.den
#check @Rat.den_pos
#check @Rat.reduced
#check @Rat.num_div_den
#check @Real.convergent
#check @Real.exists_rat_eq_convergent
#check @GenContFract.of
#check @GenContFract.convs
#check @ENNReal.ofReal
#check @ENNReal.ofReal_le_ofReal
#check @ENNReal.ofReal_le_iff_le_toReal
#check @ENNReal.lt_ofReal_iff_toReal_lt
#check @ENNReal.ofReal_toReal
#check @ENNReal.toReal_nonneg
#check @sSup_le
#check @le_sSup
#check @isLUB_sSup
#check @Set.Infinite.mono
#check @Set.Infinite.not_finite
#check @exists_between

-- Exact final signature: no additional implicit mathematical argument.
open ErdosMahlerAudit in
#check (show Gate05.SubspaceTwoThreePrimitive → Gate08.MatveevRationalThree →
    ∀ (τ : ℝ), 4 ≤ τ →
    ∃ (K : Set ℝ) (ξ : (ℕ → Bool) → ℝ) (t0 : ℕ) (f : List Bool → ℕ),
      Gate13.CantorSpec τ t0 f ξ K ∧
      Gate14.ArithmeticLowerSpec τ t0 f ξ ∧
      Gate15.UpperSpec τ t0 f ξ ∧
      (∀ x ∈ K, Irrational x ∧
        Gate16.irrationalityExponent x = ENNReal.ofReal τ ∧
        {q : ℚ | (∃ m : ℕ, q = Real.convergent x m) ∧
          (∃ A B : ℕ, q.num = (2 : ℤ)^A ∧ q.den = 3 ^ B)}.Infinite)
    from @Gate16.erdos_mahler_main)

-- The endpoint and a nonintegral parameter; no integer-order restriction.
open ErdosMahlerAudit in
#check fun hST hM => Gate16.erdos_mahler_main hST hM 4 (by norm_num)
open ErdosMahlerAudit in
#check fun hST hM => Gate16.erdos_mahler_main hST hM (9 / 2) (by norm_num)

-- Arbitrarily small positive real gaps on both sides, no uniform threshold.
open ErdosMahlerAudit in
#check fun {τ t0 f ξ} (hA : Gate14.ArithmeticLowerSpec τ t0 f ξ)
    (ε : ℕ → Bool) (η : ℝ) (hη : 0 < η) (hητ : η < τ) =>
  Gate16.approxOrder_of_infinite_good hA ε (s := τ - η) (by linarith) (by linarith)
open ErdosMahlerAudit in
#check fun {τ t0 f ξ} (hU : Gate15.UpperSpec τ t0 f ξ)
    (ε : ℕ → Bool) (η : ℝ) (hη : 0 < η) =>
  (show (Gate16.Good (ξ ε) (τ + η)).Finite from hU.finite_too_good ε (τ + η) (by linarith))

-- Denominator one can actually belong, for every real order s.
open ErdosMahlerAudit.Gate16 in
#check fun (s : ℝ) => (show (1 : ℚ) ∈ Good (3 / 2) s from by norm_num [Good])
#check (show (1 : ℚ).den = 1 from rfl)
open ErdosMahlerAudit.Gate16 in
#check fun (q : ℚ) (s : ℝ) => (show q ∉ Good (q : ℝ) s from by simp [Good])

-- Unfolded numeric definition, finite bound, lower bound without attainment, and top.
#check @ErdosMahlerAudit.Gate16.exponent_eq_sSup
#check @ErdosMahlerAudit.Gate16.exponent_le_of_finite
#check @ErdosMahlerAudit.Gate16.ofReal_le_exponent_of_infinite
#check @ErdosMahlerAudit.Gate16.exponent_eq_top_of_all_orders

set_option maxHeartbeats 8000000 in
open Lean Elab Command in
run_elab do
  let env ← getEnv
  let mut roots : Array Name := #[]
  let mut bodyCount : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "ErdosMahlerAudit.Gate16." ||
        n.toString.startsWith "_private.ErdosMahlerAudit.Gate16." then
      roots := roots.push n
      let ci ← getConstInfo n
      logInfo m!"DECL {n}\nTYPE {ci.type}"
      if ci.isUnsafe || ci.isPartial then throwError "Unsafe or partial declaration {n}"
      match ci with
      | .axiomInfo _ => throwError "Unexpected new axiom {n}"
      | .opaqueInfo _ => throwError "Unexpected opaque declaration {n}"
      | _ => pure ()
      if let some v := ci.value? true then
        bodyCount := bodyCount + 1
        logInfo m!"STORED_BODY {n}\n{v}\nDIRECT_DEPENDENCIES {ci.type.getUsedConstants ++ v.getUsedConstants}"
      else
        match ci with
        | .defnInfo _ | .thmInfo _ => throwError "Missing stored body {n}"
        | _ => pure ()
      let axs ← Lean.collectAxioms n
      logInfo m!"INDEPENDENT_AXIOMS {n}: {axs}"
      for a in axs do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
          throwError "Unexpected dependency {a} in {n}"
  logInfo m!"ALL_GATE16_DECLARATIONS_AUDITED {roots.size}; STORED_BODIES {bodyCount}"
  let edges := #[
    (``ErdosMahlerAudit.Gate16.erdos_mahler_main, ``ErdosMahlerAudit.Gate15.upper_irrationality_exponent),
    (``ErdosMahlerAudit.Gate16.erdos_mahler_main, ``ErdosMahlerAudit.Gate16.branch_exponent),
    (``ErdosMahlerAudit.Gate16.erdos_mahler_main, ``ErdosMahlerAudit.Gate14.ArithmeticLowerSpec.irrational),
    (``ErdosMahlerAudit.Gate16.erdos_mahler_main, ``ErdosMahlerAudit.Gate13.CantorSpec.range_eq),
    (``ErdosMahlerAudit.Gate16.branch_exponent, ``ErdosMahlerAudit.Gate15.UpperSpec.finite_too_good),
    (``ErdosMahlerAudit.Gate16.branch_exponent, ``ErdosMahlerAudit.Gate16.approxOrder_of_infinite_good),
    (``ErdosMahlerAudit.Gate16.approxOrder_of_infinite_good, ``ErdosMahlerAudit.Gate14.ArithmeticLowerSpec.infinite_good),
    (``ErdosMahlerAudit.Gate16.infinite_prescribed_convergents, ``ErdosMahlerAudit.Gate14.ArithmeticLowerSpec.infinite_good),
    (``ErdosMahlerAudit.Gate16.branch_exponent, ``ErdosMahlerAudit.Gate16.exponent_le_of_finite),
    (``ErdosMahlerAudit.Gate16.branch_exponent, ``ErdosMahlerAudit.Gate16.ofReal_le_exponent_of_infinite),
    (``ErdosMahlerAudit.Gate16.irrationalityExponent, ``sSup),
    (``ErdosMahlerAudit.Gate16.irrationalityExponent, ``ENNReal.ofReal),
    (``ErdosMahlerAudit.Gate16.ofReal_le_exponent_of_infinite, ``exists_between)
  ]
  for (src, dst) in edges do
    let ci ← getConstInfo src
    let some v := ci.value? true | throwError "Missing stored body {src}"
    unless v.getUsedConstants.contains dst do
      throwError "Missing stored edge {src} -> {dst}"
    logInfo m!"VERIFIED_STORED_EDGE {src} -> {dst}"
  -- Count expression-tree occurrences, including shared subterms each time.
  let finalInfo ← getConstInfo ``ErdosMahlerAudit.Gate16.erdos_mahler_main
  let some finalBody := finalInfo.value? true | throwError "Missing final body"
  let mut exprs := #[finalBody]
  let mut calls : Nat := 0
  while !exprs.isEmpty do
    let e := exprs.back!
    exprs := exprs.pop
    match e with
    | .const n _ =>
      if n == ``ErdosMahlerAudit.Gate15.upper_irrationality_exponent then calls := calls + 1
    | .app f a => exprs := exprs.push f |>.push a
    | .lam _ t b _ | .forallE _ t b _ => exprs := exprs.push t |>.push b
    | .letE _ t v b _ => exprs := exprs.push t |>.push v |>.push b
    | .mdata _ b | .proj _ _ b => exprs := exprs.push b
    | _ => pure ()
  unless calls == 1 do throwError "Expected exactly one Gate 15 call, found {calls}"
  logInfo m!"GATE15_STORED_CALL_COUNT {calls}"
  -- Every new mathematical declaration is a root, including hidden/generated ones.
  let mut pending := roots
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
      logInfo m!"TRANSITIVE_TYPE {n}: {ci.type}\nTRANSITIVE_AXIOMS {n}: {axs}"
      for d in deps do
        if d.toString.startsWith "ErdosMahlerAudit." ||
            d.toString.startsWith "_private.ErdosMahlerAudit." then
          pending := pending.push d
  for n in #[``ErdosMahlerAudit.Gate15.upper_irrationality_exponent,
      ``ErdosMahlerAudit.Gate14.prescribed_convergents_lower_exponent,
      ``ErdosMahlerAudit.Gate13.cantor_set_of_tau,
      ``ErdosMahlerAudit.Gate14.ArithmeticLowerSpec.infinite_good,
      ``ErdosMahlerAudit.Gate15.UpperSpec.finite_too_good,
      ``ErdosMahlerAudit.Gate14.branch_irrational,
      ``ErdosMahlerAudit.Gate14.regular_convergent,
      ``ErdosMahlerAudit.Gate05.SubspaceTwoThreePrimitive,
      ``ErdosMahlerAudit.Gate08.MatveevRationalThree] do
    unless seen.contains n do throwError "Missing dependency path to {n}"
    logInfo m!"VERIFIED_PUBLIC_PATH {n}"
  logInfo m!"TRANSITIVE_PROJECT_DECLARATIONS_AUDITED {seen.size}"
