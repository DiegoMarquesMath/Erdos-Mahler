module

public import ErdosMahlerAudit.Gate10.Summation
public import ErdosMahlerAudit.Gate04.SmallDenominators

/-! Proposition 2.1 with one absolute leading constant 60, TeX 1083–1092. -/

public section
namespace ErdosMahlerAudit.Gate10
open Filter
open scoped Topology

/-- The small-denominator remainder after dividing by N. -/
theorem small_remainder_identity {N : ℕ} (hN : 0 < N) :
    (N : ℝ) ^ (2 / 3 : ℝ) / (N : ℝ) = (N : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have he := Real.rpow_sub hNr (2 / 3 : ℝ) 1
  norm_num only [Real.rpow_one, show (2 / 3 : ℝ) - 1 = -(1 / 3 : ℝ) by ring] at he
  exact he.symm

theorem eventually_small_remainder {η : ℝ} (hη : 0 < η) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      60 * (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ η / 2 := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 3 by norm_num)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp
    (ht.eventually (gt_mem_nhds (show (0 : ℝ) < η / 120 by positivity)))
  exact ⟨N0, fun N hN => by have := hN0 N hN; linarith⟩

/-- The constant is selected before ν, D, and η. The only unresolved external
mathematical inputs are the two displayed ordinary arguments. -/
theorem proposition_2_1
    (hST : Gate05.SubspaceTwoThreePrimitive) (hMatveev : Gate08.MatveevRationalThree) :
    ∃ C : ℝ, C = 60 ∧ 0 < C ∧ ∀ ν D : ℝ, 4 < ν → ν ≤ 5 → 2 ≤ D →
      ∀ η : ℝ, 0 < η → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → N ∈ convergentDenominators →
        (Gate02.E N D ν : ℝ) / (N : ℝ) ≤ C * D ^ (2 - ν) + η := by
  refine ⟨60, rfl, by norm_num, ?_⟩
  intro ν D hν hν5 hD η hη
  obtain ⟨Nh, hNh⟩ := large_denominator_negligible hST hMatveev ν hν hν5
    (η / 2) (by positivity)
  obtain ⟨Nr, hNr⟩ := eventually_small_remainder hη
  refine ⟨max Nh Nr, ?_⟩
  intro N hN hND
  have hNp := Gate03.convergentDenominators_pos hND
  have hNpR : (0 : ℝ) < N := Nat.cast_pos.mpr hNp
  have hh := hNh N ((le_max_left _ _).trans hN) hND
  have hr := hNr N ((le_max_right _ _).trans hN)
  have hs := div_le_div_of_nonneg_right (Gate04.small_denominator_estimate hND hν.le hD) hNpR.le
  have he : ((Gate02.E N ((N : ℝ) ^ (1 / 3 : ℝ)) ν : ℝ) +
      60 * ((N : ℝ) * D ^ (2 - ν) + (N : ℝ) ^ (2 / 3 : ℝ))) / N =
      (Gate02.E N ((N : ℝ) ^ (1 / 3 : ℝ)) ν : ℝ) / N +
        60 * D ^ (2 - ν) + 60 * (N : ℝ) ^ (-(1 / 3 : ℝ)) := by
    rw [← small_remainder_identity hNp]
    field_simp
    ring
  rw [he] at hs
  linarith

end ErdosMahlerAudit.Gate10
