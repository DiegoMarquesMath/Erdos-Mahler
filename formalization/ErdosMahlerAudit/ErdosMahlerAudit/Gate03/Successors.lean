module

public import ErdosMahlerAudit.Gate03.Rotation
public import ErdosMahlerAudit.Gate02.AdmissibleChoices

/-! Gate 02 instantiated with proved unboundedness and rotation. The sole
remaining non-domain hypothesis is the paper's uniform exceptional count;
its constant precedes nu,D and its threshold follows fixed nu,D,eta. -/

public section
namespace ErdosMahlerAudit.Gate03

/-- Lemma 2.3 with only Proposition 2.1 remaining as an explicit hypothesis. -/
theorem counting_implies_admissible_choices
    (τ : ℝ) (hτ : 4 ≤ τ)
    (hcount : ∃ Ccount : ℝ, 0 < Ccount ∧
      ∀ ν : ℝ, 4 < ν → ν ≤ 5 → ∀ D : ℝ, 2 ≤ D →
        ∀ η : ℝ, 0 < η → ∃ N0 : ℕ, ∀ N : ℕ,
          N0 ≤ N → N ∈ convergentDenominators →
            (Gate02.E N D ν : ℝ) / (N : ℝ) ≤ Ccount * D ^ (2 - ν) + η) :
    ∃ t0 : ℕ, 0 < t0 ∧ ∀ t : ℕ, t0 ≤ t →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → N ∈ convergentDenominators →
        2 ≤ (Gate02.admissibleIndices t τ N).card := by
  exact Gate02.conditional_admissible_choices τ hτ
    ⟨6, by norm_num, fun _ ht _ hN => candidate_discrepancy hN ht hτ⟩ hcount

/-- Actual successor blocks at arbitrarily large heights. No unboundedness,
rotation, density-gap, or existence conclusion is assumed. Includes tau=4. -/
theorem counting_implies_successors
    (τ : ℝ) (hτ : 4 ≤ τ)
    (hcount : ∃ Ccount : ℝ, 0 < Ccount ∧
      ∀ ν : ℝ, 4 < ν → ν ≤ 5 → ∀ D : ℝ, 2 ≤ D →
        ∀ η : ℝ, 0 < η → ∃ N0 : ℕ, ∀ N : ℕ,
          N0 ≤ N → N ∈ convergentDenominators →
            (Gate02.E N D ν : ℝ) / (N : ℝ) ≤ Ccount * D ^ (2 - ν) + η) :
    ∃ t0 : ℕ, 0 < t0 ∧ ∀ t : ℕ, t0 ≤ t → ∀ B : ℕ,
      ∃ N : ℕ, N ∈ convergentDenominators ∧ B ≤ N ∧
        ∃ b ∈ Gate02.admissibleIndices t τ N,
          ∃ c ∈ Gate02.admissibleIndices t τ N, b ≠ c := by
  exact Gate02.conditional_successors τ hτ convergentDenominators_unbounded
    ⟨6, by norm_num, fun _ ht _ hN => candidate_discrepancy hN ht hτ⟩ hcount

end ErdosMahlerAudit.Gate03
