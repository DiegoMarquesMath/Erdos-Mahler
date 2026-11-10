module

public import ErdosMahlerAudit.Gate08.Counting

/-! Actual fiber partition and the cardinality inequality, TeX 965–984. -/

public section
namespace ErdosMahlerAudit.Gate09
open Gate06 Gate07 Gate08
open scoped BigOperators

theorem selected_fraction_fiber_sum (N : ℕ) (ν θ w : ℝ) (q : ℕ) :
    (selectedFractions N ν θ w).card =
      ∑ c ∈ selectedClasses N ν θ w q, (selectedFiber N ν θ w q c).card := by
  classical
  rw [← selectedPositive_card N ν θ w]
  exact Finset.card_eq_sum_card_image (classMap q) (selectedPositive N ν θ w)

theorem selected_card_le_class_card (hMatveev : MatveevRationalThree)
    {N : ℕ} {ν θ w : ℝ} (hθ : 1 < θ) (hθν : θ < ν / 4) (hw : 1 ≤ w)
    (hx : rigidityThreshold hMatveev ≤ Real.log ((N : ℝ) / w)) :
    ((selectedFractions N ν θ w).card : ℝ) ≤
      13 * w * (selectedClasses N ν θ w (leastPower (Real.log ((N : ℝ) / w)))).card := by
  classical
  rw [selected_fraction_fiber_sum N ν θ w (leastPower (Real.log ((N : ℝ) / w))),
    Nat.cast_sum]
  calc
    _ ≤ ∑ _c ∈ selectedClasses N ν θ w (leastPower (Real.log ((N : ℝ) / w))),
        (13 * w : ℝ) := Finset.sum_le_sum fun c _ =>
      selectedFiber_card_at_threshold hMatveev hθ hθν hw hx c
    _ = _ := by simp [mul_comm]

theorem rigidityThreshold_ge_four (hMatveev : MatveevRationalThree) :
    4 ≤ rigidityThreshold hMatveev := by
  dsimp [rigidityThreshold]
  linarith [matveevConstant_pos hMatveev]

theorem class_count_and_size_bound (hMatveev : MatveevRationalThree)
    (N : ℕ) (ν θ w : ℝ) (hN : N ∈ convergentDenominators)
    (hν4 : 4 < ν) (hν5 : ν ≤ 5) (hθ : 1 < θ) (hθν : θ < ν / 4) (hw : 1 ≤ w)
    (hx : rigidityThreshold hMatveev ≤ Real.log ((N : ℝ) / w))
    (hM : 0 < (selectedFractions N ν θ w).card) :
    ((selectedFractions N ν θ w).card : ℝ) ≤ 13 * w *
      (4 * (N : ℝ) / (selectedFractions N ν θ w).card) ^
        (3 * leastExponent (Real.log ((N : ℝ) / w))) := by
  have hx2 : 2 ≤ Real.log ((N : ℝ) / w) :=
    le_trans (by norm_num) ((rigidityThreshold_ge_four hMatveev).trans hx)
  have hc := selected_fractions_power_class_bound N ν θ w hN hν4 hν5 hθ hθν
    (by linarith) hM _ (leastExponent_pos hx2)
  exact (selected_card_le_class_card hMatveev hθ hθν hw hx).trans
    (mul_le_mul_of_nonneg_left hc (by positivity))

theorem exceptional_band_card_zero_of_selected_card_zero
    (N : ℕ) (ν θ w : ℝ) (hN : N ∈ convergentDenominators)
    (hν4 : 4 < ν) (hν5 : ν ≤ 5) (hθ : 1 < θ) (hθν : θ < ν / 4) (hw : 1 ≤ w)
    (hM : (selectedFractions N ν θ w).card = 0) :
    (exceptionalBand N ν θ w).card = 0 := by
  have h := exceptional_band_multiplicity N ν θ w hN hν4 hν5 hθ hθν (by linarith)
  omega

end ErdosMahlerAudit.Gate09
