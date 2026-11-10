module

public import ErdosMahlerAudit.Gate09.Decay

/-! Lemma 3.6 for the exact exceptional band, TeX 952–1005. -/

public section
namespace ErdosMahlerAudit.Gate09
open Gate06 Gate08

theorem denominator_range_at_threshold (hMatveev : MatveevRationalThree)
    (N : ℕ) (ν θ w : ℝ) (hN : N ∈ convergentDenominators)
    (hν4 : 4 < ν) (hν5 : ν ≤ 5) (hθ : 1 < θ) (hθν : θ < ν / 4) (hw : 1 ≤ w)
    (hx : rigidityThreshold hMatveev ≤ Real.log ((N : ℝ) / w)) :
    ((exceptionalBand N ν θ w).card : ℝ) / (N : ℝ) ≤
      16 * Real.exp (-(1 / 52 : ℝ) * Real.log ((N : ℝ) / w) /
        Real.log (2 + Real.log ((N : ℝ) / w))) := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (Gate03.convergentDenominators_pos hN)
  have hw0 : 0 < w := by linarith
  have hx4 : 4 ≤ Real.log ((N : ℝ) / w) := (rigidityThreshold_ge_four hMatveev).trans hx
  have hx2 : 2 ≤ Real.log ((N : ℝ) / w) := by linarith
  by_cases hM : (selectedFractions N ν θ w).card = 0
  · rw [exceptional_band_card_zero_of_selected_card_zero N ν θ w hN hν4 hν5 hθ hθν hw hM]
    simp only [Nat.cast_zero, zero_div]
    positivity
  · have hMpos : 0 < (selectedFractions N ν θ w).card := Nat.pos_of_ne_zero hM
    have hMR : (0 : ℝ) < (selectedFractions N ν θ w).card := Nat.cast_pos.mpr hMpos
    have hy : 0 < ((selectedFractions N ν θ w).card : ℝ) / (4 * (N : ℝ)) := by positivity
    have hcount := class_count_and_size_bound hMatveev N ν θ w hN hν4 hν5 hθ hθν hw hx hMpos
    have hp := normalized_power_bound hMR hN0 hcount
    rw [inverse_ratio_exp hN0 hw0] at hp
    have hroot := root_exp_bound hy (by omega : 0 < 3 * leastExponent (Real.log ((N : ℝ) / w)) + 1)
      (hp.trans (coefficient_absorption hx4))
    have hdecay := hroot.trans (uniform_exp_bound hx2)
    have hmult : ((exceptionalBand N ν θ w).card : ℝ) ≤
        4 * ((selectedFractions N ν θ w).card : ℝ) := by
      exact_mod_cast exceptional_band_multiplicity N ν θ w hN hν4 hν5 hθ hθν hw0
    calc
      _ ≤ (4 * ((selectedFractions N ν θ w).card : ℝ)) / (N : ℝ) :=
        div_le_div_of_nonneg_right hmult hN0.le
      _ = 16 * (((selectedFractions N ν θ w).card : ℝ) / (4 * (N : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hdecay (by norm_num)

/-- The absolute constants precede every band parameter; Matveev is the sole external input. -/
theorem denominator_range_bound (hMatveev : MatveevRationalThree) :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < x₀ ∧
      ∀ (N : ℕ) (ν θ w : ℝ),
        N ∈ convergentDenominators → 4 < ν → ν ≤ 5 → 1 < θ → θ < ν / 4 →
        1 ≤ w → x₀ ≤ Real.log ((N : ℝ) / w) →
        ((exceptionalBand N ν θ w).card : ℝ) / (N : ℝ) ≤
          C * Real.exp (-c * Real.log ((N : ℝ) / w) /
            Real.log (2 + Real.log ((N : ℝ) / w))) := by
  refine ⟨1 / 52, 16, rigidityThreshold hMatveev, by norm_num, by norm_num,
    rigidityThreshold_pos hMatveev, ?_⟩
  exact denominator_range_at_threshold hMatveev

end ErdosMahlerAudit.Gate09
