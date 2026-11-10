module

public import ErdosMahlerAudit.RationalArithmetic

/-! Gate 02 reuses Gate 01's `Exceptional`, including its exact canonical
denominator and exponent domain. Filters are classical, not algorithms. -/

@[expose] public section

namespace ErdosMahlerAudit.Gate02

noncomputable def badIndices (N : ℕ) (D ν : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Ico N (2 * N)).filter
    (fun b => ∃ s : ℚ, Exceptional b ν s ∧ D < (s.den : ℝ))

noncomputable def E (N : ℕ) (D ν : ℝ) : ℕ := (badIndices N D ν).card

theorem E_eq_exceptionalCount (N : ℕ) (D ν : ℝ) :
    E N D ν = exceptionalCount N D ν := rfl

theorem mem_badIndices {N b : ℕ} {D ν : ℝ} :
    b ∈ badIndices N D ν ↔
      N ≤ b ∧ b < 2 * N ∧ ∃ s : ℚ, Exceptional b ν s ∧ D < (s.den : ℝ) := by
  classical
  simp [badIndices, and_assoc]

theorem exceptional_canonical {b : ℕ} {ν : ℝ} {s : ℚ}
    (h : Exceptional b ν s) :
    0 < s.den ∧ Nat.Coprime s.num.natAbs s.den ∧ (0 : ℚ) < s :=
  ⟨s.pos, s.reduced, lt_of_lt_of_le (by norm_num) h.2.2.2.1⟩

end ErdosMahlerAudit.Gate02
