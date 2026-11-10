module

public import ErdosMahlerAudit.Gate04.TruncatedCounting

/-! Lemma 3.1, TeX 487–529, with the existing Gate02.E and constant 60. -/

public section
namespace ErdosMahlerAudit.Gate04

/-- The manuscript's high-cutoff case directly from Gate 01 monotonicity. -/
theorem E_le_of_cutoff_le (N : ℕ) (ν : ℝ) {D U : ℝ} (hUD : U ≤ D) :
    Gate02.E N D ν ≤ Gate02.E N U ν := by
  simpa only [Gate02.E_eq_exceptionalCount] using exceptionalCount_antitone N ν hUD

/-- Explicit constant version; the proof also works at ν=4 and above ν=5.
The exceptional predicate itself is unchanged and retains 4<ν≤5. -/
theorem small_denominator_estimate {N : ℕ} (hN : N ∈ convergentDenominators)
    {ν D : ℝ} (hν : 4 ≤ ν) (hD : 2 ≤ D) :
    (Gate02.E N D ν : ℝ) ≤
      (Gate02.E N ((N : ℝ) ^ (1 / 3 : ℝ)) ν : ℝ) +
        60 * ((N : ℝ) * D ^ (2 - ν) + (N : ℝ) ^ (2 / 3 : ℝ)) := by
  have hnonneg : 0 ≤ 60 * ((N : ℝ) * D ^ (2 - ν) + (N : ℝ) ^ (2 / 3 : ℝ)) := by
    have hDp : 0 ≤ D := by linarith
    positivity
  by_cases hhigh : (N : ℝ) ^ (1 / 3 : ℝ) ≤ D
  · have h : (Gate02.E N D ν : ℝ) ≤ Gate02.E N ((N : ℝ) ^ (1 / 3 : ℝ)) ν := by
      exact_mod_cast E_le_of_cutoff_le N ν hhigh
    linarith
  · have hsplit : (Gate02.E N D ν : ℝ) ≤
        (Gate02.E N ((N : ℝ) ^ (1 / 3 : ℝ)) ν : ℝ) +
          (boundedIndices N D ((N : ℝ) ^ (1 / 3 : ℝ)) ν).card := by
      exact_mod_cast E_le_high_add_bounded N D ((N : ℝ) ^ (1 / 3 : ℝ)) ν
    have hsmall := boundedIndices_card_le (U := (N : ℝ) ^ (1 / 3 : ℝ)) hN hD hν
    have he : ((N : ℝ) ^ (1 / 3 : ℝ)) ^ (2 : ℕ) = (N : ℝ) ^ (2 / 3 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
      norm_num
    rw [he] at hsmall
    linarith

/-- Exactly the Gate 04 contract: C is chosen before ν,D,N, with no extra
mathematical hypotheses or eventual-height restriction. -/
theorem small_denominator_absolute :
    ∃ C : ℝ, 0 < C ∧ ∀ (ν D : ℝ) (N : ℕ),
      4 < ν → ν ≤ 5 → 2 ≤ D → N ∈ convergentDenominators →
        (Gate02.E N D ν : ℝ) ≤
          (Gate02.E N ((N : ℝ) ^ (1 / 3 : ℝ)) ν : ℝ) +
            C * ((N : ℝ) * D ^ (2 - ν) + (N : ℝ) ^ (2 / 3 : ℝ)) :=
  ⟨60, by norm_num, fun _ _ _ hν _ hD hN => small_denominator_estimate hN hν.le hD⟩

end ErdosMahlerAudit.Gate04
