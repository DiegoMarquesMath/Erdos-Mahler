module

import all ErdosMahlerAudit.Gate11.Intervals
import all ErdosMahlerAudit.Gate11.Separation
import all ErdosMahlerAudit.Gate11.Successors
public import ErdosMahlerAudit.Gate11.Successors
public import Lean

/-! Exact interfaces, boundary instances, and stored-value dependency checks
for the finite successor-interval construction. -/

set_option format.width 110
set_option pp.fullNames true

-- Inherited definitions and the actual selection theorem.
#check @ErdosMahlerAudit.Gate10.two_successors
#check @ErdosMahlerAudit.Gate02.admissibleIndices
#check @ErdosMahlerAudit.Gate02.mem_admissibleIndices
#check @ErdosMahlerAudit.Gate02.J
#check @ErdosMahlerAudit.Gate02.radius_eq_Q
#check @ErdosMahlerAudit.R_den
#check @ErdosMahlerAudit.R_num
#check @ErdosMahlerAudit.R_injective
#check @ErdosMahlerAudit.R_mem_Ioo
#check @ErdosMahlerAudit.rational_separation
#print ErdosMahlerAudit.Gate05.SubspaceTwoThreePrimitive
#print ErdosMahlerAudit.Gate08.MatveevRationalThree

#check @ErdosMahlerAudit.Gate11.left
#print axioms ErdosMahlerAudit.Gate11.left
#check @ErdosMahlerAudit.Gate11.right
#print axioms ErdosMahlerAudit.Gate11.right
#check @ErdosMahlerAudit.Gate11.K
#print axioms ErdosMahlerAudit.Gate11.K
#check @ErdosMahlerAudit.Gate11.J_eq
#print axioms ErdosMahlerAudit.Gate11.J_eq
#check @ErdosMahlerAudit.Gate11.left_lt_right
#print axioms ErdosMahlerAudit.Gate11.left_lt_right
#check @ErdosMahlerAudit.Gate11.interior_K
#print axioms ErdosMahlerAudit.Gate11.interior_K
#check @ErdosMahlerAudit.Gate11.width_eq
#print axioms ErdosMahlerAudit.Gate11.width_eq
#check @ErdosMahlerAudit.Gate11.radius_decay
#print axioms ErdosMahlerAudit.Gate11.radius_decay
#check @ErdosMahlerAudit.Gate11.radius_strictAnti
#print axioms ErdosMahlerAudit.Gate11.radius_strictAnti
#check @ErdosMahlerAudit.Gate11.radius_le_fourth
#print axioms ErdosMahlerAudit.Gate11.radius_le_fourth
#check @ErdosMahlerAudit.Gate11.radius_extension_lt
#print axioms ErdosMahlerAudit.Gate11.radius_extension_lt
#check @ErdosMahlerAudit.Gate11.endpoints_mem_Ioo
#print axioms ErdosMahlerAudit.Gate11.endpoints_mem_Ioo
#check @ErdosMahlerAudit.Gate11.K_subset_Ioo
#print axioms ErdosMahlerAudit.Gate11.K_subset_Ioo
#check @ErdosMahlerAudit.Gate11.nested_endpoints
#print axioms ErdosMahlerAudit.Gate11.nested_endpoints
#check @ErdosMahlerAudit.Gate11.K_subset_interior
#print axioms ErdosMahlerAudit.Gate11.K_subset_interior
#check @ErdosMahlerAudit.Gate11.width_contraction
#print axioms ErdosMahlerAudit.Gate11.width_contraction
#check @ErdosMahlerAudit.Gate11.common_denominator
#print axioms ErdosMahlerAudit.Gate11.common_denominator
#check @ErdosMahlerAudit.Gate11.common_denominator_separation
#print axioms ErdosMahlerAudit.Gate11.common_denominator_separation
#check @ErdosMahlerAudit.Gate11.separation_chain
#print axioms ErdosMahlerAudit.Gate11.separation_chain
#check @ErdosMahlerAudit.Gate11.strictly_separated
#print axioms ErdosMahlerAudit.Gate11.strictly_separated
#check @ErdosMahlerAudit.Gate11.K_disjoint
#print axioms ErdosMahlerAudit.Gate11.K_disjoint
#check @ErdosMahlerAudit.Gate11.ordered_successors
#print axioms ErdosMahlerAudit.Gate11.ordered_successors
#check @ErdosMahlerAudit.Gate11.nested_disjoint_successor_intervals
#print axioms ErdosMahlerAudit.Gate11.nested_disjoint_successor_intervals

#print ErdosMahlerAudit.Gate11.left
#print ErdosMahlerAudit.Gate11.right
#print ErdosMahlerAudit.Gate11.K

open ErdosMahlerAudit ErdosMahlerAudit.Gate11

-- The boundary τ = 4, t = 1 is included, and equality of siblings is excluded.
#check (show Gate02.radius 1 4 = 1 / 81 from by
  norm_num [Gate02.radius, Real.rpow_neg])
#check endpoints_mem_Ioo (t := 1) (τ := 4) (by norm_num) (by norm_num)
#check radius_decay (t := 1) (d := 2) (τ := 4) (by norm_num) (by norm_num)
#check width_contraction (t := 1) (d := 2) (τ := 4) (by norm_num) (by norm_num)
#check separation_chain (τ := 4) (b := 2) (c := 3)
  (by norm_num) (by norm_num) (by norm_num) (by norm_num)
#check (show ∀ b : ℕ, ¬ b < b from fun b => lt_irrefl b)
#check fun hST hMatveev => nested_disjoint_successor_intervals hST hMatveev 4 (by norm_num)

-- Audit actual stored bodies and reject any additional foundational axiom.
open Lean Elab Command in
run_elab do
  let names := #[
    ``ErdosMahlerAudit.Gate11.left,
    ``ErdosMahlerAudit.Gate11.right,
    ``ErdosMahlerAudit.Gate11.K,
    ``ErdosMahlerAudit.Gate11.J_eq,
    ``ErdosMahlerAudit.Gate11.left_lt_right,
    ``ErdosMahlerAudit.Gate11.interior_K,
    ``ErdosMahlerAudit.Gate11.width_eq,
    ``ErdosMahlerAudit.Gate11.radius_decay,
    ``ErdosMahlerAudit.Gate11.radius_strictAnti,
    ``ErdosMahlerAudit.Gate11.radius_le_fourth,
    ``ErdosMahlerAudit.Gate11.radius_extension_lt,
    ``ErdosMahlerAudit.Gate11.endpoints_mem_Ioo,
    ``ErdosMahlerAudit.Gate11.K_subset_Ioo,
    ``ErdosMahlerAudit.Gate11.nested_endpoints,
    ``ErdosMahlerAudit.Gate11.K_subset_interior,
    ``ErdosMahlerAudit.Gate11.width_contraction,
    ``ErdosMahlerAudit.Gate11.common_denominator,
    ``ErdosMahlerAudit.Gate11.common_denominator_separation,
    ``ErdosMahlerAudit.Gate11.separation_chain,
    ``ErdosMahlerAudit.Gate11.strictly_separated,
    ``ErdosMahlerAudit.Gate11.K_disjoint,
    ``ErdosMahlerAudit.Gate11.ordered_successors,
    ``ErdosMahlerAudit.Gate11.nested_disjoint_successor_intervals
  ]
  for n in names do
    let ci ← getConstInfo n
    logInfo m!"DECL {n}"
    logInfo m!"TYPE {ci.type}"
    let some v := ci.value? true | throwError "Stored body unavailable for {n}"
    let deps := v.getUsedConstants
    logInfo m!"DIRECT_PROJECT_DEPENDENCIES {deps.filter fun d =>
      d.toString.startsWith "ErdosMahlerAudit."}"
    if n == ``ErdosMahlerAudit.Gate11.ordered_successors then
      unless deps.contains ``ErdosMahlerAudit.Gate10.two_successors do
        throwError "Actual Gate 10 selection theorem missing from stored proof"
    let axs ← Lean.collectAxioms n
    logInfo m!"AXIOMS {axs}"
    for a in axs do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "Unexpected foundational dependency {a} in {n}"
