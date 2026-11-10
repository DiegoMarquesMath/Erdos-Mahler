module

public import ErdosMahlerAudit.Gate10.Series
public import ErdosMahlerAudit.Gate10.Bands
public import ErdosMahlerAudit.Gate09.DenominatorRange

/-! Finite summation against the convergent tail, TeX 1061–1080. -/

public section
namespace ErdosMahlerAudit.Gate10
open scoped BigOperators

/-- Gate09's actual constants, rewritten on the exact logarithmic scale. -/
theorem band_count_le_majorant (hMatveev : Gate08.MatveevRationalThree)
    {N j : ℕ} {ν θ : ℝ} (hN : N ∈ convergentDenominators)
    (hν : 4 < ν) (hν5 : ν ≤ 5) (hθ : 1 < θ) (hθν : θ < ν / 4)
    (hw : 1 ≤ heightScale N θ j)
    (hx : Gate08.rigidityThreshold hMatveev ≤ (j : ℝ) * Real.log θ) :
    ((Gate06.exceptionalBand N ν θ (heightScale N θ j)).card : ℝ) / (N : ℝ) ≤
      16 * bandMajorant θ j := by
  have he := heightScale_log_ratio (Gate03.convergentDenominators_pos hN)
    (show 0 < θ by linarith) j
  have hb := Gate09.denominator_range_at_threshold hMatveev N ν θ (heightScale N θ j)
    hN hν hν5 hθ hθν hw (by rwa [he])
  rw [he] at hb
  convert hb using 1
  unfold bandMajorant
  congr 2
  ring

/-- High-denominator exceptions have density zero along the actual convergent
 denominators, conditional on precisely the two explicit external inputs. -/
theorem large_denominator_negligible
    (hST : Gate05.SubspaceTwoThreePrimitive) (hMatveev : Gate08.MatveevRationalThree)
    (ν : ℝ) (hν : 4 < ν) (hν5 : ν ≤ 5) (η : ℝ) (hη : 0 < η) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → N ∈ convergentDenominators →
      (Gate02.E N ((N : ℝ) ^ (1 / 3 : ℝ)) ν : ℝ) / (N : ℝ) ≤ η := by
  classical
  let θ := chosenTheta ν
  obtain ⟨hθ, hθν⟩ := chosenTheta_admissible hν
  have hh : 0 < Real.log θ := Real.log_pos hθ
  obtain ⟨J₀, hJ₀⟩ := bandMajorant_finite_tail hθ (show 0 < η / 16 by positivity)
  obtain ⟨J₁, hJ₁⟩ := exists_nat_ge (Gate08.rigidityThreshold hMatveev / Real.log θ)
  let J := max J₀ J₁
  have hthreshold (j : ℕ) (hj : J ≤ j) :
      Gate08.rigidityThreshold hMatveev ≤ (j : ℝ) * Real.log θ := by
    have hj' : (J₁ : ℝ) ≤ j := Nat.cast_le.mpr ((le_max_right _ _).trans hj)
    exact (div_le_iff₀ hh).mp (hJ₁.trans hj')
  obtain ⟨Na, hNa⟩ := eventually_active_ge hST hν hν5 hθ J
  obtain ⟨Nw, hNw⟩ := eventually_active_height_ge_one
  obtain ⟨Nc, hNc⟩ := eventually_height_lt_N hST hν hν5
  refine ⟨max 2 (max Na (max Nw Nc)), ?_⟩
  intro N hN hND
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNaN : Na ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNwN : Nw ≤ N := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hNcN : Nc ≤ N := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  obtain ⟨K, hK⟩ := high_count_le_finite_band_sum (ν := ν) (by omega) hθ
    (hNc N hNcN hND).le
  let s := (Finset.range K).filter (fun j =>
    (Gate06.exceptionalBand N ν θ (heightScale N θ j)).Nonempty)
  have hactive (j : ℕ) (hj : j ∈ s) :
      (Gate06.exceptionalBand N ν θ (heightScale N θ j)).Nonempty :=
    (Finset.mem_filter.mp hj).2
  have htail : (∑ j ∈ s, bandMajorant θ j) < η / 16 :=
    hJ₀ s (fun j hj => (le_max_left _ _).trans (hNa N hNaN hND j (hactive j hj)))
  have hsum : (∑ j ∈ s, (Gate06.exceptionalBand N ν θ (heightScale N θ j)).card) =
      ∑ j ∈ Finset.range K, (Gate06.exceptionalBand N ν θ (heightScale N θ j)).card := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j hj hjs
    apply Finset.card_eq_zero.mpr
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro ha
    exact hjs (Finset.mem_filter.mpr ⟨hj, ha⟩)
  rw [← hsum] at hK
  have hKr : (Gate02.E N ((N : ℝ) ^ (1 / 3 : ℝ)) ν : ℝ) ≤
      ∑ j ∈ s, ((Gate06.exceptionalBand N ν θ (heightScale N θ j)).card : ℝ) := by
    exact_mod_cast hK
  calc
    _ ≤ (∑ j ∈ s, ((Gate06.exceptionalBand N ν θ (heightScale N θ j)).card : ℝ)) / N :=
      div_le_div_of_nonneg_right hKr hNp.le
    _ = ∑ j ∈ s, ((Gate06.exceptionalBand N ν θ (heightScale N θ j)).card : ℝ) / N :=
      Finset.sum_div _ _ _
    _ ≤ ∑ j ∈ s, 16 * bandMajorant θ j := by
      apply Finset.sum_le_sum
      intro j hj
      exact band_count_le_majorant hMatveev hND hν hν5 hθ hθν
        (hNw N hNwN ν θ _ hθ (hactive j hj))
        (hthreshold j (hNa N hNaN hND j (hactive j hj)))
    _ = 16 * ∑ j ∈ s, bandMajorant θ j := (Finset.mul_sum _ _ _).symm
    _ ≤ η := by linarith

end ErdosMahlerAudit.Gate10
