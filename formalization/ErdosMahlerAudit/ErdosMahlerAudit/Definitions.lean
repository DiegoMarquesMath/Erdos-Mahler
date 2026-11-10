module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Frozen manuscript definitions (Section 2)

The manuscript uses positive natural indices. Definitions are total on `ℕ`;
claims that need positivity explicitly assume `0 < b`. `R` is a canonical `ℚ`,
not a floating point value or an unevaluated pair of integers.
-/

@[expose] public section

namespace ErdosMahlerAudit

noncomputable def alpha : ℝ := Real.log 3 / Real.log 2

noncomputable def a (b : ℕ) : ℕ := ⌈(b : ℝ) * alpha⌉₊

noncomputable def R (b : ℕ) : ℚ := (2 : ℚ) ^ a b / (3 : ℚ) ^ b

noncomputable def Phi (y : ℝ) : ℝ := 1 - Real.log y / Real.log 2

/-- Denominators of the regular continued-fraction convergents of `alpha`. -/
noncomputable def convergentDenominators : Set ℕ :=
  Set.range (fun n : ℕ => (Real.convergent alpha n).den)

/-- The exponent domain is part of the manuscript's exceptional condition.
The canonical numerator and positive denominator of `s : ℚ` encode reducedness. -/
def Exceptional (b : ℕ) (ν : ℝ) (s : ℚ) : Prop :=
  0 < b ∧ 4 < ν ∧ ν ≤ 5 ∧ (1 : ℚ) ≤ s ∧ s ≤ 2 ∧ s ≠ R b ∧
    |(R b : ℝ) - (s : ℝ)| < 1 / (16 * (s.den : ℝ) ^ ν)

/-- Counts indices, not exceptional fractions; the denominator cutoff is real. -/
noncomputable def exceptionalCount (N : ℕ) (D ν : ℝ) : ℕ := by
  classical
  exact ((Finset.Ico N (2 * N)).filter
    (fun b => ∃ s : ℚ, Exceptional b ν s ∧ D < (s.den : ℝ))).card

end ErdosMahlerAudit
