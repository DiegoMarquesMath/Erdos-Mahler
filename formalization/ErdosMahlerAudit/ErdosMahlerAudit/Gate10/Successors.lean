module

public import ErdosMahlerAudit.Gate10.Proposition
public import ErdosMahlerAudit.Gate03.Successors

/-! Optional Lemma 2.3 corollary. This makes no Cantor-set assertion. -/

public section
namespace ErdosMahlerAudit.Gate10

theorem two_successors
    (hST : Gate05.SubspaceTwoThreePrimitive) (hMatveev : Gate08.MatveevRationalThree)
    (τ : ℝ) (hτ : 4 ≤ τ) :
    ∃ t0 : ℕ, 0 < t0 ∧ ∀ t : ℕ, t0 ≤ t → ∀ B : ℕ,
      ∃ N : ℕ, N ∈ convergentDenominators ∧ B ≤ N ∧
        ∃ b ∈ Gate02.admissibleIndices t τ N,
          ∃ c ∈ Gate02.admissibleIndices t τ N, b ≠ c := by
  obtain ⟨C, _, hC, hcount⟩ := proposition_2_1 hST hMatveev
  exact Gate03.counting_implies_successors τ hτ
    ⟨C, hC, fun ν hν hν5 D hD => hcount ν D hν hν5 hD⟩

end ErdosMahlerAudit.Gate10
