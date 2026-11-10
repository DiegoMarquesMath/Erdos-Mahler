module

public import ErdosMahlerAudit.Gate08.Height
public import ErdosMahlerAudit.Gate08.PowerSize
public import ErdosMahlerAudit.Gate08.LogError

/-! Weighted coefficient estimates with explicit absolute constants, TeX 900–919. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate08
open Gate06

noncomputable def weightedSize (b c q : ℕ) (w : ℝ) : ℝ :=
  max 1 (max (|(a c : ℝ) - (a b : ℝ)| * Real.log 2 / (3 * w / q))
    (max (|(c : ℝ) - (b : ℝ)| * Real.log 3 / (3 * w / q)) (q : ℝ)))

theorem band_coefficient_bounds {N b c : ℕ} {ν θ w : ℝ}
    (hb : b ∈ exceptionalBand N ν θ w) (hc : c ∈ exceptionalBand N ν θ w) :
    |(c : ℝ) - (b : ℝ)| < N ∧
      |(a c : ℝ) - (a b : ℝ)| ≤ alpha * N + 1 := by
  have hb' := mem_exceptionalBand.mp hb
  have hc' := mem_exceptionalBand.mp hc
  have hbN : (N : ℝ) ≤ b := by exact_mod_cast hb'.1
  have hcN : (N : ℝ) ≤ c := by exact_mod_cast hc'.1
  have hb2 : (b : ℝ) < 2 * N := by exact_mod_cast hb'.2.1
  have hc2 : (c : ℝ) < 2 * N := by exact_mod_cast hc'.2.1
  have hd : |(c : ℝ) - (b : ℝ)| < N := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hab : (b : ℝ) * alpha ≤ a b := Nat.le_ceil _
  have hac : (c : ℝ) * alpha ≤ a c := Nat.le_ceil _
  have hab' : (a b : ℝ) < (b : ℝ) * alpha + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg b) alpha_pos.le)
  have hac' : (a c : ℝ) < (c : ℝ) * alpha + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg c) alpha_pos.le)
  refine ⟨hd, abs_le.mpr ⟨?_, ?_⟩⟩ <;>
    nlinarith [mul_nonneg (sub_nonneg.mpr (abs_lt.mp hd).1.le) alpha_pos.le,
      mul_nonneg (sub_nonneg.mpr (abs_lt.mp hd).2.le) alpha_pos.le]

theorem weightedSize_bounds {N b c q : ℕ} {ν θ w : ℝ}
    (hb : b ∈ exceptionalBand N ν θ w) (hc : c ∈ exceptionalBand N ν θ w)
    (hq : 1 ≤ q) (hw : 1 ≤ w) (hNw : w ≤ N) :
    1 ≤ weightedSize b c q w ∧ weightedSize b c q w ≤ q * N / w := by
  have hw0 : 0 < w := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hN1 : (1 : ℝ) ≤ N := hw.trans hNw
  have ha3 : 0 < 3 * w / (q : ℝ) := by positivity
  have hcoef := band_coefficient_bounds hb hc
  have h2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have h3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have ha : alpha * Real.log 2 = Real.log 3 := div_mul_cancel₀ _ log_two_pos.ne'
  have hc1 : |(a c : ℝ) - (a b : ℝ)| * Real.log 2 ≤ 3 * N := by
    have h := mul_le_mul_of_nonneg_right hcoef.2 log_two_pos.le
    have hN0 : (0 : ℝ) ≤ N := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h3 hN0, ha]
  have hc2 : |(c : ℝ) - (b : ℝ)| * Real.log 3 ≤ 3 * N := by
    have h := mul_le_mul_of_nonneg_right hcoef.1.le log_three_pos.le
    nlinarith [mul_le_mul_of_nonneg_right h3 (Nat.cast_nonneg N)]
  have hh : (q : ℝ) ≤ q * N / w := by
    apply (le_div_iff₀ hw0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hNw hq0.le]
  have hratio (z : ℝ) (hz : z ≤ 3 * N) : z / (3 * w / q) ≤ q * N / w := by
    apply (div_le_iff₀ ha3).mpr
    calc
      z ≤ 3 * N := hz
      _ = (q * N / w) * (3 * w / q) := by field_simp
  exact ⟨le_max_left _ _, max_le (hq1.trans hh)
    (max_le (hratio _ hc1) (max_le (hratio _ hc2) hh))⟩

theorem large_x_implies_w_le {N : ℕ} {w : ℝ} (hN : 0 < N) (hw : 0 < w)
    (hx : 2 ≤ Real.log ((N : ℝ) / w)) : w ≤ N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : 1 ≤ (N : ℝ) / w :=
    (Real.log_nonneg_iff (div_pos hN0 hw)).mp (by linarith)
  simpa only [one_mul] using (le_div_iff₀ hw).mp hr

theorem weightedSize_log_bound {N b c : ℕ} {ν θ w : ℝ}
    (hb : b ∈ exceptionalBand N ν θ w) (hc : c ∈ exceptionalBand N ν θ w)
    (hw : 1 ≤ w) (hx : 2 ≤ Real.log ((N : ℝ) / w)) :
    1 + Real.log (weightedSize b c (leastPower (Real.log ((N : ℝ) / w))) w) ≤
      3 * Real.log ((N : ℝ) / w) := by
  let x := Real.log ((N : ℝ) / w)
  have hw0 : 0 < w := by linarith
  have hN : 0 < N := by
    have h := mem_exceptionalBand.mp hb
    omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hbds := weightedSize_bounds hb hc (leastPower_pos x) hw
    (large_x_implies_w_le hN hw0 hx)
  have hq0 : (0 : ℝ) < leastPower x := by exact_mod_cast leastPower_pos x
  have hl := Real.log_le_log (by linarith [hbds.1]) hbds.2
  have hid : Real.log ((leastPower x : ℝ) * N / w) = Real.log (leastPower x : ℝ) + x := by
    rw [mul_div_assoc, Real.log_mul hq0.ne' (div_pos hN0 hw0).ne']
  rw [hid] at hl
  have hx0 : 0 < x := by dsimp [x]; linarith
  have hlx := Real.log_le_sub_one_of_pos hx0
  have hlq := leastPower_log hx
  have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  dsimp [x] at *
  linarith

end ErdosMahlerAudit.Gate08
