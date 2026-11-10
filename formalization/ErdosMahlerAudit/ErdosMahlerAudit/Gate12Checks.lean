module

import all ErdosMahlerAudit.Gate12.Selection
import all ErdosMahlerAudit.Gate12.Tree
public import ErdosMahlerAudit.Gate12.Tree
public import Lean

/-! Exact types, transparent certificates, boundary cases and stored-proof audit. -/

set_option format.width 110
set_option pp.fullNames true

#check @ErdosMahlerAudit.Gate11.nested_disjoint_successor_intervals
#check @ErdosMahlerAudit.Gate02.mem_admissibleIndices
#print ErdosMahlerAudit.Gate02.admissibleIndices
#print ErdosMahlerAudit.convergentDenominators
#print ErdosMahlerAudit.Gate05.SubspaceTwoThreePrimitive
#print ErdosMahlerAudit.Gate08.MatveevRationalThree

#print ErdosMahlerAudit.Gate12.PairSpec
#print ErdosMahlerAudit.Gate12.Selection
#print ErdosMahlerAudit.Gate12.TreeSpec

#check @ErdosMahlerAudit.Gate12.width
#print axioms ErdosMahlerAudit.Gate12.width

#check @ErdosMahlerAudit.Gate12.width_pos
#print axioms ErdosMahlerAudit.Gate12.width_pos

#check @ErdosMahlerAudit.Gate12.selection_exists
#print axioms ErdosMahlerAudit.Gate12.selection_exists

#check @ErdosMahlerAudit.Gate12.selected
#print axioms ErdosMahlerAudit.Gate12.selected

#check @ErdosMahlerAudit.Gate12.leftChild
#print axioms ErdosMahlerAudit.Gate12.leftChild

#check @ErdosMahlerAudit.Gate12.rightChild
#print axioms ErdosMahlerAudit.Gate12.rightChild

#check @ErdosMahlerAudit.Gate12.node
#print axioms ErdosMahlerAudit.Gate12.node

#check @ErdosMahlerAudit.Gate12.node_nil
#print axioms ErdosMahlerAudit.Gate12.node_nil

#check @ErdosMahlerAudit.Gate12.node_append
#print axioms ErdosMahlerAudit.Gate12.node_append

#check @ErdosMahlerAudit.Gate12.node_false
#print axioms ErdosMahlerAudit.Gate12.node_false

#check @ErdosMahlerAudit.Gate12.node_true
#print axioms ErdosMahlerAudit.Gate12.node_true

#check @ErdosMahlerAudit.Gate12.node_height
#print axioms ErdosMahlerAudit.Gate12.node_height

#check @ErdosMahlerAudit.Gate12.root_le_node
#print axioms ErdosMahlerAudit.Gate12.root_le_node

#check @ErdosMahlerAudit.Gate12.node_pair
#print axioms ErdosMahlerAudit.Gate12.node_pair

#check @ErdosMahlerAudit.Gate12.node_domain
#print axioms ErdosMahlerAudit.Gate12.node_domain

#check @ErdosMahlerAudit.Gate12.node_step
#print axioms ErdosMahlerAudit.Gate12.node_step

#check @ErdosMahlerAudit.Gate12.decay_denominator_pos
#print axioms ErdosMahlerAudit.Gate12.decay_denominator_pos

#check @ErdosMahlerAudit.Gate12.node_width_bound
#print axioms ErdosMahlerAudit.Gate12.node_width_bound

#check @ErdosMahlerAudit.Gate12.binary_tree_of_intervals
#print axioms ErdosMahlerAudit.Gate12.binary_tree_of_intervals

#print ErdosMahlerAudit.Gate12.width
#print ErdosMahlerAudit.Gate12.selected
#print ErdosMahlerAudit.Gate12.leftChild
#print ErdosMahlerAudit.Gate12.rightChild
#print ErdosMahlerAudit.Gate12.node
#print ErdosMahlerAudit.Gate12.binary_tree_of_intervals

open ErdosMahlerAudit in
#check (show Gate05.SubspaceTwoThreePrimitive → Gate08.MatveevRationalThree →
  ∀ τ : ℝ, 4 ≤ τ → ∃ t0 : ℕ, ∃ f : List Bool → ℕ, Gate12.TreeSpec τ t0 f from
  Gate12.binary_tree_of_intervals)

open ErdosMahlerAudit in
#check fun hST hMatveev => Gate12.binary_tree_of_intervals hST hMatveev 4 (by norm_num)

#check ErdosMahlerAudit.Gate12.decay_denominator_pos 0
#check (show (81 : ℝ) ^ (0 + 1) = 81 from by norm_num)

-- Obtain the stored values, inspect their actual constants, and recursively audit axioms.
open Lean Elab Command in
run_elab do
  let names := #[
    ``ErdosMahlerAudit.Gate12.width,
    ``ErdosMahlerAudit.Gate12.width_pos,
    ``ErdosMahlerAudit.Gate12.selection_exists,
    ``ErdosMahlerAudit.Gate12.selected,
    ``ErdosMahlerAudit.Gate12.leftChild,
    ``ErdosMahlerAudit.Gate12.rightChild,
    ``ErdosMahlerAudit.Gate12.node,
    ``ErdosMahlerAudit.Gate12.node_nil,
    ``ErdosMahlerAudit.Gate12.node_append,
    ``ErdosMahlerAudit.Gate12.node_false,
    ``ErdosMahlerAudit.Gate12.node_true,
    ``ErdosMahlerAudit.Gate12.node_height,
    ``ErdosMahlerAudit.Gate12.root_le_node,
    ``ErdosMahlerAudit.Gate12.node_pair,
    ``ErdosMahlerAudit.Gate12.node_domain,
    ``ErdosMahlerAudit.Gate12.node_step,
    ``ErdosMahlerAudit.Gate12.decay_denominator_pos,
    ``ErdosMahlerAudit.Gate12.node_width_bound,
    ``ErdosMahlerAudit.Gate12.binary_tree_of_intervals
  ]
  for n in names do
    let ci ← getConstInfo n
    logInfo m!"DECL {n}"
    logInfo m!"TYPE {ci.type}"
    let some v := ci.value? true | throwError "Stored body unavailable for {n}"
    let deps := v.getUsedConstants
    logInfo m!"DIRECT_PROJECT_DEPENDENCIES {deps.filter fun d =>
      d.toString.startsWith "ErdosMahlerAudit."}"
    let axs ← Lean.collectAxioms n
    logInfo m!"AXIOMS {axs}"
    for a in axs do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "Unexpected foundational dependency {a} in {n}"
  let edges := #[
    (``ErdosMahlerAudit.Gate12.binary_tree_of_intervals, ``ErdosMahlerAudit.Gate12.selected),
    (``ErdosMahlerAudit.Gate12.binary_tree_of_intervals, ``ErdosMahlerAudit.Gate12.node_pair),
    (``ErdosMahlerAudit.Gate12.binary_tree_of_intervals, ``ErdosMahlerAudit.Gate12.node_width_bound),
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
  -- Also cover generated structure declarations and auxiliary definitions.
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    if n.toString.startsWith "ErdosMahlerAudit.Gate12." then
      count := count + 1
      match ci with
      | .axiomInfo _ => throwError "Unexpected axiom declaration {n}"
      | .opaqueInfo _ => throwError "Unexpected opaque declaration {n}"
      | _ => pure ()
      for a in (← Lean.collectAxioms n) do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
          throwError "Unexpected foundational dependency {a} in {n}"
  logInfo m!"ALL_GATE12_DECLARATIONS_AUDITED {count}"
