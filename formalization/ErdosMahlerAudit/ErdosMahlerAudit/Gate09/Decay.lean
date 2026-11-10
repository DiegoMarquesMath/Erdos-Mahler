module

public import ErdosMahlerAudit.Gate09.Counting

/-! Normalization and uniform exponential decay, TeX 985–1000. -/

public section
namespace ErdosMahlerAudit.Gate09
open Gate08

theorem inverse_ratio_exp {N w : ℝ} (hN : 0 < N) (hw : 0 < w) :
    w / N = Real.exp (-Real.log (N / w)) := by
  rw [Real.exp_neg, Real.exp_log (div_pos hN hw), inv_div]

/-- Multiplying by the positive reciprocal power preserves the extra exponent one. -/
theorem normalized_power_bound {M N w : ℝ} {k : ℕ}
    (hM : 0 < M) (hN : 0 < N)
    (h : M ≤ 13 * w * (4 * N / M) ^ (3 * k)) :
    (M / (4 * N)) ^ (3 * k + 1) ≤ (13 / 4 : ℝ) * (w / N) := by
  have h4N : 0 < 4 * N := by positivity
  have hy : 0 < M / (4 * N) := div_pos hM h4N
  have hc : (4 * N / M) ^ (3 * k) * (M / (4 * N)) ^ (3 * k) = 1 := by
    rw [← mul_pow]
    field_simp
    exact one_pow _
  have hh := mul_le_mul_of_nonneg_right h (pow_nonneg hy.le (3 * k))
  rw [mul_assoc, hc, mul_one] at hh
  calc
    _ = (M * (M / (4 * N)) ^ (3 * k)) / (4 * N) := by
      rw [pow_succ]
      ring
    _ ≤ (13 * w) / (4 * N) := div_le_div_of_nonneg_right hh h4N.le
    _ = _ := by ring

theorem coefficient_absorption {x : ℝ} (hx : 4 ≤ x) :
    (13 / 4 : ℝ) * Real.exp (-x) ≤ Real.exp (-x / 2) := by
  have hc : (13 / 4 : ℝ) ≤ Real.exp (x / 2) := by
    have h := Real.two_mul_le_exp (x := x / 2)
    linarith
  calc
    _ ≤ Real.exp (x / 2) * Real.exp (-x) :=
      mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem least_exponent_log_denominator {x : ℝ} (hx : 2 ≤ x) :
    ((3 * leastExponent x + 1 : ℕ) : ℝ) ≤ 26 * Real.log (2 + x) := by
  have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this
    exact this
  have htwo : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlx := Real.log_le_log (by linarith : 0 < x) (by linarith : x ≤ 2 + x)
  have hl2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ 2 + x)
  have hk := leastExponent_log_bound hx
  have hkn : (0 : ℝ) ≤ leastExponent x := Nat.cast_nonneg _
  have hkh := mul_le_mul_of_nonneg_left hhalf hkn
  push_cast
  nlinarith

theorem root_exp_bound {y x : ℝ} {m : ℕ} (hy : 0 < y) (hm : 0 < m)
    (h : y ^ m ≤ Real.exp (-x / 2)) :
    y ≤ Real.exp (-x / (2 * (m : ℝ))) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hl := Real.log_le_log (pow_pos hy m) h
  rw [Real.log_pow, Real.log_exp] at hl
  apply (Real.log_le_iff_le_exp hy).mp
  apply (le_div_iff₀ (by positivity : 0 < 2 * (m : ℝ))).mpr
  nlinarith

theorem uniform_exp_bound {x : ℝ} (hx : 2 ≤ x) :
    Real.exp (-x / (2 * ((3 * leastExponent x + 1 : ℕ) : ℝ))) ≤
      Real.exp (-(1 / 52 : ℝ) * x / Real.log (2 + x)) := by
  have hm : (0 : ℝ) < (3 * leastExponent x + 1 : ℕ) := by positivity
  have hl : 0 < Real.log (2 + x) := Real.log_pos (by linarith)
  have hb := least_exponent_log_denominator hx
  apply Real.exp_le_exp.mpr
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * ((3 * leastExponent x + 1 : ℕ) : ℝ)) hl).mpr
  nlinarith [mul_nonneg (by linarith : 0 ≤ x)
    (sub_nonneg.mpr hb)]

end ErdosMahlerAudit.Gate09
