module

-- Reveal inherited private proof bodies for the recursive audit.
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
public import ErdosMahlerAudit.Gate13.Topology
public import Lean

/-! Exact interfaces, boundary checks and independent stored-declaration audit. -/

set_option format.width 110
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000

#check @ErdosMahlerAudit.Gate11.K
#check @ErdosMahlerAudit.Gate11.left
#check @ErdosMahlerAudit.Gate11.right
#check @ErdosMahlerAudit.Gate12.PairSpec
#check @ErdosMahlerAudit.Gate12.TreeSpec
#check @ErdosMahlerAudit.Gate12.binary_tree_of_intervals
#print ErdosMahlerAudit.Gate11.K
#print ErdosMahlerAudit.Gate11.left
#print ErdosMahlerAudit.Gate11.right
#print ErdosMahlerAudit.Gate02.radius
#print ErdosMahlerAudit.Gate12.PairSpec
#print ErdosMahlerAudit.Gate12.TreeSpec
#print ErdosMahlerAudit.Gate05.SubspaceTwoThreePrimitive
#print ErdosMahlerAudit.Gate08.MatveevRationalThree
#check @ErdosMahlerAudit.Gate13.CantorSpec
#print ErdosMahlerAudit.Gate13.CantorSpec
set_option pp.explicit true in
#print ErdosMahlerAudit.Gate13.CantorSpec
#print axioms ErdosMahlerAudit.Gate13.CantorSpec

#synth TopologicalSpace (ℕ → Bool)
#synth DiscreteTopology Bool
#synth CompactSpace (ℕ → Bool)
#synth TotallyDisconnectedSpace (ℕ → Bool)

#check @ErdosMahlerAudit.Gate13.«prefix»
#print axioms ErdosMahlerAudit.Gate13.«prefix»

#check @ErdosMahlerAudit.Gate13.prefix_zero
#print axioms ErdosMahlerAudit.Gate13.prefix_zero

#check @ErdosMahlerAudit.Gate13.prefix_succ
#print axioms ErdosMahlerAudit.Gate13.prefix_succ

#check @ErdosMahlerAudit.Gate13.prefix_length
#print axioms ErdosMahlerAudit.Gate13.prefix_length

#check @ErdosMahlerAudit.Gate13.prefix_eq_iff
#print axioms ErdosMahlerAudit.Gate13.prefix_eq_iff

#check @ErdosMahlerAudit.Gate13.first_divergence
#print axioms ErdosMahlerAudit.Gate13.first_divergence

#check @ErdosMahlerAudit.Gate13.prefix_cylinder
#print axioms ErdosMahlerAudit.Gate13.prefix_cylinder

#check @ErdosMahlerAudit.Gate13.isOpen_prefix
#print axioms ErdosMahlerAudit.Gate13.isOpen_prefix

#check @ErdosMahlerAudit.Gate13.flip
#print axioms ErdosMahlerAudit.Gate13.flip

#check @ErdosMahlerAudit.Gate13.flip_ne
#print axioms ErdosMahlerAudit.Gate13.flip_ne

#check @ErdosMahlerAudit.Gate13.prefix_flip
#print axioms ErdosMahlerAudit.Gate13.prefix_flip

#check @ErdosMahlerAudit.Gate13.interval
#print axioms ErdosMahlerAudit.Gate13.interval

#check @ErdosMahlerAudit.Gate13.interval_nonempty
#print axioms ErdosMahlerAudit.Gate13.interval_nonempty

#check @ErdosMahlerAudit.Gate13.interval_closed
#print axioms ErdosMahlerAudit.Gate13.interval_closed

#check @ErdosMahlerAudit.Gate13.interval_compact
#print axioms ErdosMahlerAudit.Gate13.interval_compact

#check @ErdosMahlerAudit.Gate13.interval_strict_nested
#print axioms ErdosMahlerAudit.Gate13.interval_strict_nested

#check @ErdosMahlerAudit.Gate13.interval_nested
#print axioms ErdosMahlerAudit.Gate13.interval_nested

#check @ErdosMahlerAudit.Gate13.interval_antitone
#print axioms ErdosMahlerAudit.Gate13.interval_antitone

#check @ErdosMahlerAudit.Gate13.interval_subset_root
#print axioms ErdosMahlerAudit.Gate13.interval_subset_root

#check @ErdosMahlerAudit.Gate13.branch_height
#print axioms ErdosMahlerAudit.Gate13.branch_height

#check @ErdosMahlerAudit.Gate13.branch_width_bound
#print axioms ErdosMahlerAudit.Gate13.branch_width_bound

#check @ErdosMahlerAudit.Gate13.width_bound_pos
#print axioms ErdosMahlerAudit.Gate13.width_bound_pos

#check @ErdosMahlerAudit.Gate13.width_bound_tendsto
#print axioms ErdosMahlerAudit.Gate13.width_bound_tendsto

#check @ErdosMahlerAudit.Gate13.width_bound_small
#print axioms ErdosMahlerAudit.Gate13.width_bound_small

#check @ErdosMahlerAudit.Gate13.interval_distance
#print axioms ErdosMahlerAudit.Gate13.interval_distance

#check @ErdosMahlerAudit.Gate13.unique_limit
#print axioms ErdosMahlerAudit.Gate13.unique_limit

#check @ErdosMahlerAudit.Gate13.point
#print axioms ErdosMahlerAudit.Gate13.point

#check @ErdosMahlerAudit.Gate13.point_mem
#print axioms ErdosMahlerAudit.Gate13.point_mem

#check @ErdosMahlerAudit.Gate13.point_interior
#print axioms ErdosMahlerAudit.Gate13.point_interior

#check @ErdosMahlerAudit.Gate13.point_endpoints
#print axioms ErdosMahlerAudit.Gate13.point_endpoints

#check @ErdosMahlerAudit.Gate13.point_displacement
#print axioms ErdosMahlerAudit.Gate13.point_displacement

#check @ErdosMahlerAudit.Gate13.point_prefix_bound
#print axioms ErdosMahlerAudit.Gate13.point_prefix_bound

#check @ErdosMahlerAudit.Gate13.point_continuous
#print axioms ErdosMahlerAudit.Gate13.point_continuous

#check @ErdosMahlerAudit.Gate13.point_injective
#print axioms ErdosMahlerAudit.Gate13.point_injective

#check @ErdosMahlerAudit.Gate13.cantorImage
#print axioms ErdosMahlerAudit.Gate13.cantorImage

#check @ErdosMahlerAudit.Gate13.image_nonempty
#print axioms ErdosMahlerAudit.Gate13.image_nonempty

#check @ErdosMahlerAudit.Gate13.image_subset
#print axioms ErdosMahlerAudit.Gate13.image_subset

#check @ErdosMahlerAudit.Gate13.image_compact
#print axioms ErdosMahlerAudit.Gate13.image_compact

#check @ErdosMahlerAudit.Gate13.image_closed
#print axioms ErdosMahlerAudit.Gate13.image_closed

#check @ErdosMahlerAudit.Gate13.image_homeomorph
#print axioms ErdosMahlerAudit.Gate13.image_homeomorph

#check @ErdosMahlerAudit.Gate13.image_homeomorph_coe
#print axioms ErdosMahlerAudit.Gate13.image_homeomorph_coe

#check @ErdosMahlerAudit.Gate13.image_no_isolated
#print axioms ErdosMahlerAudit.Gate13.image_no_isolated

#check @ErdosMahlerAudit.Gate13.image_totallyDisconnected
#print axioms ErdosMahlerAudit.Gate13.image_totallyDisconnected

#check @ErdosMahlerAudit.Gate13.image_interior_empty
#print axioms ErdosMahlerAudit.Gate13.image_interior_empty

#check @ErdosMahlerAudit.Gate13.image_closure_interior_empty
#print axioms ErdosMahlerAudit.Gate13.image_closure_interior_empty

#check @ErdosMahlerAudit.Gate13.cantor_set_from_tree
#print axioms ErdosMahlerAudit.Gate13.cantor_set_from_tree

#check @ErdosMahlerAudit.Gate13.cantor_set_of_tau
set_option pp.explicit true in
#check @ErdosMahlerAudit.Gate13.cantor_set_of_tau
#print axioms ErdosMahlerAudit.Gate13.cantor_set_of_tau

#check @ErdosMahlerAudit.Gate13.width_bound_formula
#print axioms ErdosMahlerAudit.Gate13.width_bound_formula

#check @ErdosMahlerAudit.Gate13.point_agreement_bound
#print axioms ErdosMahlerAudit.Gate13.point_agreement_bound

open ErdosMahlerAudit in
#check (show Gate05.SubspaceTwoThreePrimitive → Gate08.MatveevRationalThree →
  ∀ τ : ℝ, 4 ≤ τ →
    ∃ (K : Set ℝ) (ξ : (ℕ → Bool) → ℝ) (t0 : ℕ) (f : List Bool → ℕ),
      Gate13.CantorSpec τ t0 f ξ K from @Gate13.cantor_set_of_tau)

open ErdosMahlerAudit in
#check fun hST hMatveev => Gate13.cantor_set_of_tau hST hMatveev 4 (by norm_num)

open ErdosMahlerAudit in
#check (show ∀ (τ : ℝ) (t0 : ℕ),
  Gate12.width τ t0 / (81 : ℝ) ^ 0 = Gate12.width τ t0 from by simp)

#check ErdosMahlerAudit.Gate13.width_bound_pos 4 1 0
#check ErdosMahlerAudit.Gate13.width_bound_tendsto 4 1
#check ErdosMahlerAudit.Gate13.prefix_zero
#check ErdosMahlerAudit.Gate13.point_interior

set_option maxHeartbeats 1600000 in
-- Print all stored bodies and independently traverse hundreds of inherited declarations.
open Lean Elab Command in
run_elab do
  let names := #[
    ``ErdosMahlerAudit.Gate13.point_agreement_bound,
    ``ErdosMahlerAudit.Gate13.width_bound_formula,
    ``ErdosMahlerAudit.Gate13.«prefix»,
    ``ErdosMahlerAudit.Gate13.prefix_zero,
    ``ErdosMahlerAudit.Gate13.prefix_succ,
    ``ErdosMahlerAudit.Gate13.prefix_length,
    ``ErdosMahlerAudit.Gate13.prefix_eq_iff,
    ``ErdosMahlerAudit.Gate13.first_divergence,
    ``ErdosMahlerAudit.Gate13.prefix_cylinder,
    ``ErdosMahlerAudit.Gate13.isOpen_prefix,
    ``ErdosMahlerAudit.Gate13.flip,
    ``ErdosMahlerAudit.Gate13.flip_ne,
    ``ErdosMahlerAudit.Gate13.prefix_flip,
    ``ErdosMahlerAudit.Gate13.interval,
    ``ErdosMahlerAudit.Gate13.interval_nonempty,
    ``ErdosMahlerAudit.Gate13.interval_closed,
    ``ErdosMahlerAudit.Gate13.interval_compact,
    ``ErdosMahlerAudit.Gate13.interval_strict_nested,
    ``ErdosMahlerAudit.Gate13.interval_nested,
    ``ErdosMahlerAudit.Gate13.interval_antitone,
    ``ErdosMahlerAudit.Gate13.interval_subset_root,
    ``ErdosMahlerAudit.Gate13.branch_height,
    ``ErdosMahlerAudit.Gate13.branch_width_bound,
    ``ErdosMahlerAudit.Gate13.width_bound_pos,
    ``ErdosMahlerAudit.Gate13.width_bound_tendsto,
    ``ErdosMahlerAudit.Gate13.width_bound_small,
    ``ErdosMahlerAudit.Gate13.interval_distance,
    ``ErdosMahlerAudit.Gate13.unique_limit,
    ``ErdosMahlerAudit.Gate13.point,
    ``ErdosMahlerAudit.Gate13.point_mem,
    ``ErdosMahlerAudit.Gate13.point_interior,
    ``ErdosMahlerAudit.Gate13.point_endpoints,
    ``ErdosMahlerAudit.Gate13.point_displacement,
    ``ErdosMahlerAudit.Gate13.point_prefix_bound,
    ``ErdosMahlerAudit.Gate13.point_continuous,
    ``ErdosMahlerAudit.Gate13.point_injective,
    ``ErdosMahlerAudit.Gate13.cantorImage,
    ``ErdosMahlerAudit.Gate13.image_nonempty,
    ``ErdosMahlerAudit.Gate13.image_subset,
    ``ErdosMahlerAudit.Gate13.image_compact,
    ``ErdosMahlerAudit.Gate13.image_closed,
    ``ErdosMahlerAudit.Gate13.image_homeomorph,
    ``ErdosMahlerAudit.Gate13.image_homeomorph_coe,
    ``ErdosMahlerAudit.Gate13.image_no_isolated,
    ``ErdosMahlerAudit.Gate13.image_totallyDisconnected,
    ``ErdosMahlerAudit.Gate13.image_interior_empty,
    ``ErdosMahlerAudit.Gate13.image_closure_interior_empty,
    ``ErdosMahlerAudit.Gate13.cantor_set_from_tree,
    ``ErdosMahlerAudit.Gate13.cantor_set_of_tau
  ]
  for n in names do
    let ci ← getConstInfo n
    logInfo m!"DECL {n}"
    logInfo m!"TYPE {ci.type}"
    let some v := ci.value? true | throwError "Stored body unavailable for {n}"
    logInfo m!"STORED_BODY {n}: {v}"
    let deps := (ci.type.getUsedConstants ++ v.getUsedConstants).filter fun d =>
      d.toString.startsWith "ErdosMahlerAudit."
    logInfo m!"DIRECT_PROJECT_DEPENDENCIES {deps}"
    let axs ← Lean.collectAxioms n
    logInfo m!"AXIOMS {axs}"
    for a in axs do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "Unexpected foundational dependency {a} in {n}"
  let edges := #[
    (``ErdosMahlerAudit.Gate13.cantor_set_of_tau,
      ``ErdosMahlerAudit.Gate12.binary_tree_of_intervals),
    (``ErdosMahlerAudit.Gate13.cantor_set_of_tau,
      ``ErdosMahlerAudit.Gate13.cantor_set_from_tree),
    (``ErdosMahlerAudit.Gate13.cantor_set_from_tree,
      ``ErdosMahlerAudit.Gate13.point_continuous),
    (``ErdosMahlerAudit.Gate13.cantor_set_from_tree,
      ``ErdosMahlerAudit.Gate13.point_injective),
    (``ErdosMahlerAudit.Gate13.point, ``ErdosMahlerAudit.Gate13.unique_limit),
    (``ErdosMahlerAudit.Gate13.point_interior,
      ``ErdosMahlerAudit.Gate13.interval_strict_nested),
    (``ErdosMahlerAudit.Gate13.point_injective, ``ErdosMahlerAudit.Gate12.PairSpec.disjoint),
    (``ErdosMahlerAudit.Gate13.image_no_isolated, ``ErdosMahlerAudit.Gate13.prefix_flip),
    (``ErdosMahlerAudit.Gate12.binary_tree_of_intervals, ``ErdosMahlerAudit.Gate12.selected),
    (``ErdosMahlerAudit.Gate12.selected, ``ErdosMahlerAudit.Gate12.selection_exists),
    (``ErdosMahlerAudit.Gate12.selection_exists,
      ``ErdosMahlerAudit.Gate11.nested_disjoint_successor_intervals)
  ]
  for (src, dst) in edges do
    let ci ← getConstInfo src
    let some v := ci.value? true | throwError "Missing stored body: {src}"
    unless v.getUsedConstants.contains dst do
      throwError "Missing stored proof dependency {src} -> {dst}"
    logInfo m!"VERIFIED_STORED_EDGE {src} -> {dst}"
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    if n.toString.startsWith "ErdosMahlerAudit.Gate13." then
      count := count + 1
      match ci with
      | .axiomInfo _ => throwError "Unexpected axiom declaration {n}"
      | .opaqueInfo _ => throwError "Unexpected opaque declaration {n}"
      | _ => pure ()
      for a in (← Lean.collectAxioms n) do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
          throwError "Unexpected foundational dependency {a} in {n}"
  logInfo m!"ALL_GATE13_DECLARATIONS_AUDITED {count}"
  -- Independently traverse project constants in actual types and stored values.
  let mut pending := #[``ErdosMahlerAudit.Gate13.cantor_set_of_tau]
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      let ci ← getConstInfo n
      match ci with
      | .axiomInfo _ => throwError "Project axiom on dependency path: {n}"
      | .opaqueInfo _ => throwError "Opaque project declaration on dependency path: {n}"
      | _ => pure ()
      let mut deps := ci.type.getUsedConstants
      if let some v := ci.value? true then
        deps := deps ++ v.getUsedConstants
      else
        match ci with
        | .defnInfo _ | .thmInfo _ => throwError "Missing project body: {n}"
        | _ => pure ()
      for d in deps do
        if d.toString.startsWith "ErdosMahlerAudit." then
          pending := pending.push d
  unless seen.contains ``ErdosMahlerAudit.Gate12.binary_tree_of_intervals do
    throwError "Public theorem has no stored path to the actual Gate 12 theorem"
  logInfo m!"TRANSITIVE_PROJECT_DECLARATIONS_AUDITED {seen.size}"
