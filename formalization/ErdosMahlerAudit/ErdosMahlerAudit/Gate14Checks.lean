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
public import ErdosMahlerAudit.Gate14.Theorem
public import Lean

/-! Reproducible Gate 14 interfaces, boundary checks, and stored-body audit. -/

set_option format.width 110
set_option pp.fullNames true

#check @ErdosMahlerAudit.R
#check @ErdosMahlerAudit.Gate11.K
#check @ErdosMahlerAudit.Gate12.TreeSpec
#check @ErdosMahlerAudit.Gate12.PairSpec
#check @ErdosMahlerAudit.Gate13.CantorSpec
#check @ErdosMahlerAudit.Gate13.cantor_set_of_tau
#check @ErdosMahlerAudit.Gate13.«prefix»
#check @ErdosMahlerAudit.Gate13.branch_height
#check @ErdosMahlerAudit.Gate13.point_displacement
#check @ErdosMahlerAudit.R_num
#check @ErdosMahlerAudit.R_den
#check @ErdosMahlerAudit.R_coprime
#check @ErdosMahlerAudit.rational_separation
#print ErdosMahlerAudit.R
#print ErdosMahlerAudit.Gate12.TreeSpec
#print ErdosMahlerAudit.Gate12.PairSpec
#print ErdosMahlerAudit.Gate13.CantorSpec
#print Real.convergent
#check @Real.exists_rat_eq_convergent
#check @Real.convs_eq_convergent
#print axioms Real.exists_rat_eq_convergent
#print axioms Real.convs_eq_convergent

#print ErdosMahlerAudit.Gate05.SubspaceTwoThreePrimitive
#print ErdosMahlerAudit.Gate08.MatveevRationalThree
#print ErdosMahlerAudit.Gate14.t
#print ErdosMahlerAudit.Gate14.Q
#print ErdosMahlerAudit.Gate14.r
#print ErdosMahlerAudit.Gate14.ArithmeticLowerSpec
#print Real.convergent_zero
#print Real.convergent_succ
#print GenContFract.of

#check @ErdosMahlerAudit.Gate14.r_num
#print axioms ErdosMahlerAudit.Gate14.r_num

#check @ErdosMahlerAudit.Gate14.r_den
#print axioms ErdosMahlerAudit.Gate14.r_den

#check @ErdosMahlerAudit.Gate14.r_reduced
#print axioms ErdosMahlerAudit.Gate14.r_reduced

#check @ErdosMahlerAudit.Gate14.r_eq
#print axioms ErdosMahlerAudit.Gate14.r_eq

#check @ErdosMahlerAudit.Gate14.Q_pos
#print axioms ErdosMahlerAudit.Gate14.Q_pos

#check @ErdosMahlerAudit.Gate14.radius_eq
#print axioms ErdosMahlerAudit.Gate14.radius_eq

#check @ErdosMahlerAudit.Gate14.t_zero
#print axioms ErdosMahlerAudit.Gate14.t_zero

#check @ErdosMahlerAudit.Gate14.t_height
#print axioms ErdosMahlerAudit.Gate14.t_height

#check @ErdosMahlerAudit.Gate14.t_pos
#print axioms ErdosMahlerAudit.Gate14.t_pos

#check @ErdosMahlerAudit.Gate14.t_step
#print axioms ErdosMahlerAudit.Gate14.t_step

#check @ErdosMahlerAudit.Gate14.t_strictMono
#print axioms ErdosMahlerAudit.Gate14.t_strictMono

#check @ErdosMahlerAudit.Gate14.Q_three_le
#print axioms ErdosMahlerAudit.Gate14.Q_three_le

#check @ErdosMahlerAudit.Gate14.Q_strictMono
#print axioms ErdosMahlerAudit.Gate14.Q_strictMono

#check @ErdosMahlerAudit.Gate14.Q_step
#print axioms ErdosMahlerAudit.Gate14.Q_step

#check @ErdosMahlerAudit.Gate14.Q_triple
#print axioms ErdosMahlerAudit.Gate14.Q_triple

#check @ErdosMahlerAudit.Gate14.Q_tendsto
#print axioms ErdosMahlerAudit.Gate14.Q_tendsto

#check @ErdosMahlerAudit.Gate14.Q_real_tendsto
#print axioms ErdosMahlerAudit.Gate14.Q_real_tendsto

#check @ErdosMahlerAudit.Gate14.r_injective
#print axioms ErdosMahlerAudit.Gate14.r_injective

#check @ErdosMahlerAudit.Gate14.r_range_infinite
#print axioms ErdosMahlerAudit.Gate14.r_range_infinite

#check @ErdosMahlerAudit.Gate14.displacement
#print axioms ErdosMahlerAudit.Gate14.displacement

#check @ErdosMahlerAudit.Gate14.displacement_pos
#print axioms ErdosMahlerAudit.Gate14.displacement_pos

#check @ErdosMahlerAudit.Gate14.legendre_constant
#print axioms ErdosMahlerAudit.Gate14.legendre_constant

#check @ErdosMahlerAudit.Gate14.legendre_chain
#print axioms ErdosMahlerAudit.Gate14.legendre_chain

#check @ErdosMahlerAudit.Gate14.regular_convergent
#print axioms ErdosMahlerAudit.Gate14.regular_convergent

#check @ErdosMahlerAudit.Gate14.regular_convs
#print axioms ErdosMahlerAudit.Gate14.regular_convs

#check @ErdosMahlerAudit.Gate14.infinitely_many_good_convergents
#print axioms ErdosMahlerAudit.Gate14.infinitely_many_good_convergents

#check @ErdosMahlerAudit.Gate14.branch_irrational
#print axioms ErdosMahlerAudit.Gate14.branch_irrational

#check @ErdosMahlerAudit.Gate14.eventually_constant_absorbed
#print axioms ErdosMahlerAudit.Gate14.eventually_constant_absorbed

#check @ErdosMahlerAudit.Gate14.eventually_approximation
#print axioms ErdosMahlerAudit.Gate14.eventually_approximation

#check @ErdosMahlerAudit.Gate14.approximation_threshold
#print axioms ErdosMahlerAudit.Gate14.approximation_threshold

#check @ErdosMahlerAudit.Gate14.arithmetic_from_cantor
#print axioms ErdosMahlerAudit.Gate14.arithmetic_from_cantor

#check @ErdosMahlerAudit.Gate14.prescribed_convergents_lower_exponent
#print axioms ErdosMahlerAudit.Gate14.prescribed_convergents_lower_exponent

#print ErdosMahlerAudit.Gate14.prescribed_convergents_lower_exponent
#print ErdosMahlerAudit.Gate14.regular_convergent

-- Adversarial boundary specializations, including arbitrary closeness to τ.
open ErdosMahlerAudit in
#check fun hST hMatveev => Gate14.prescribed_convergents_lower_exponent hST hMatveev 4 (by norm_num)
open ErdosMahlerAudit in
#check Gate14.legendre_constant (q := 3) (τ := 4) (by norm_num) (by norm_num)
open ErdosMahlerAudit in
#check (show (3 : ℝ) * 3 ^ (-(4 : ℝ)) < 1 / (2 * (3 : ℝ) ^ 2) from by norm_num)
open ErdosMahlerAudit in
#check fun {τ t0 f ξ K} (hC : Gate13.CantorSpec τ t0 f ξ K) (hτ : 4 ≤ τ) ε =>
  Gate14.legendre_chain hC hτ ε 0
open ErdosMahlerAudit in
#check fun {τ t0 f ξ K} (hC : Gate13.CantorSpec τ t0 f ξ K) ε
    (δ : ℝ) (hδ : 0 < δ) =>
  Gate14.approximation_threshold hC ε (s := τ - δ) (by linarith)

set_option maxHeartbeats 2000000 in
open Lean Elab Command in
run_elab do
  let env ← getEnv
  let mut count : Nat := 0
  let mut bodyCount : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "ErdosMahlerAudit.Gate14." then
      let ci ← getConstInfo n
      count := count + 1
      logInfo m!"DECL {n}\nTYPE {ci.type}"
      match ci with
      | .axiomInfo _ => throwError "Unexpected new axiom {n}"
      | .opaqueInfo _ => throwError "Unexpected opaque surrogate {n}"
      | _ => pure ()
      if let some v := ci.value? true then
        bodyCount := bodyCount + 1
        let deps := (ci.type.getUsedConstants ++ v.getUsedConstants).filter fun d =>
          d.toString.startsWith "ErdosMahlerAudit." ||
          d == ``Real.exists_rat_eq_convergent || d == ``Real.convs_eq_convergent
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
  logInfo m!"ALL_GATE14_DECLARATIONS_AUDITED {count}; STORED_BODIES {bodyCount}"
  let edges := #[
    (``ErdosMahlerAudit.Gate14.prescribed_convergents_lower_exponent,
      ``ErdosMahlerAudit.Gate13.cantor_set_of_tau),
    (``ErdosMahlerAudit.Gate14.prescribed_convergents_lower_exponent,
      ``ErdosMahlerAudit.Gate14.arithmetic_from_cantor),
    (``ErdosMahlerAudit.Gate14.arithmetic_from_cantor,
      ``ErdosMahlerAudit.Gate14.branch_irrational),
    (``ErdosMahlerAudit.Gate14.arithmetic_from_cantor,
      ``ErdosMahlerAudit.Gate14.regular_convergent),
    (``ErdosMahlerAudit.Gate14.arithmetic_from_cantor,
      ``ErdosMahlerAudit.Gate14.approximation_threshold),
    (``ErdosMahlerAudit.Gate14.branch_irrational, ``ErdosMahlerAudit.rational_separation),
    (``ErdosMahlerAudit.Gate14.branch_irrational,
      ``ErdosMahlerAudit.Gate14.eventually_approximation),
    (``ErdosMahlerAudit.Gate14.branch_irrational,
      ``ErdosMahlerAudit.Gate14.Q_real_tendsto),
    (``ErdosMahlerAudit.Gate14.regular_convergent, ``Real.exists_rat_eq_convergent),
    (``ErdosMahlerAudit.Gate14.regular_convs, ``Real.convs_eq_convergent),
    (``Real.exists_rat_eq_convergent, ``Real.exists_rat_eq_convergent'),
    (``ErdosMahlerAudit.Gate14.displacement, ``ErdosMahlerAudit.Gate13.CantorSpec.displacement),
    (``ErdosMahlerAudit.Gate14.t_step, ``ErdosMahlerAudit.Gate12.TreeSpec.pairs),
    (``ErdosMahlerAudit.Gate14.t_height, ``ErdosMahlerAudit.Gate13.branch_height)
  ]
  for (src, dst) in edges do
    let ci ← getConstInfo src
    let some v := ci.value? true | throwError "Missing stored body {src}"
    unless v.getUsedConstants.contains dst do
      throwError "Missing stored edge {src} -> {dst}"
    logInfo m!"VERIFIED_STORED_EDGE {src} -> {dst}"
  let mut pending := #[``ErdosMahlerAudit.Gate14.prescribed_convergents_lower_exponent]
  let mut seen : NameSet := {}
  let mut library : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      let ci ← getConstInfo n
      match ci with
      | .axiomInfo _ => throwError "Project axiom on dependency path {n}"
      | .opaqueInfo _ => throwError "Opaque project body on dependency path {n}"
      | _ => pure ()
      let mut deps := ci.type.getUsedConstants
      if let some v := ci.value? true then
        deps := deps ++ v.getUsedConstants
      else
        match ci with
        | .defnInfo _ | .thmInfo _ => throwError "Missing inherited body {n}"
        | _ => pure ()
      for d in deps do
        if d.toString.startsWith "ErdosMahlerAudit." then
          pending := pending.push d
        else
          library := library.insert d
  for n in #[``ErdosMahlerAudit.Gate13.cantor_set_of_tau,
      ``ErdosMahlerAudit.Gate14.branch_irrational,
      ``ErdosMahlerAudit.Gate14.regular_convergent,
      ``ErdosMahlerAudit.rational_separation,
      ``ErdosMahlerAudit.Gate14.eventually_constant_absorbed,
      ``ErdosMahlerAudit.R_den, ``ErdosMahlerAudit.R_num] do
    unless seen.contains n do throwError "Missing public dependency path to {n}"
    logInfo m!"VERIFIED_PUBLIC_PATH {n}"
  for n in #[``Real.exists_rat_eq_convergent, ``Real.convs_eq_convergent] do
    unless library.contains n do throwError "Missing public library path to {n}"
    let ci ← getConstInfo n
    unless (ci.value? true).isSome do throwError "Missing library theorem body {n}"
    logInfo m!"VERIFIED_PUBLIC_LIBRARY_PATH {n}"
  logInfo m!"TRANSITIVE_PROJECT_DECLARATIONS_AUDITED {seen.size}"
