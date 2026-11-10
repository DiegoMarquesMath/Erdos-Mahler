module

public import ErdosMahlerAudit.Gate05.SmoothPart

/-! Exact specialized product in the external contract, TeX 588–596. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate05

noncomputable def localProduct (x y : ℕ) : ℝ :=
  |(x : ℝ) - (y : ℝ)| * (y : ℝ) / (smoothPart (x * y) : ℝ)

theorem e_cast (b : ℕ) (s : ℚ) :
    (e b s : ℝ) = |(P b : ℝ) * v s - (S b : ℝ) * u s| := by
  simp only [e, Nat.cast_natAbs, Int.cast_abs, Int.cast_sub, Int.cast_mul,
    Int.cast_natCast, Nat.cast_mul]

theorem U_real (b : ℕ) (s : ℚ) :
    (U b s : ℝ) = (P b : ℝ) * v s / d b s := by
  apply (eq_div_iff (by exact_mod_cast (d_pos b s).ne')).mpr
  have h : (d b s : ℝ) * U b s = (P b : ℝ) * v s := by exact_mod_cast d_mul_U b s
  nlinarith

theorem W_real (b : ℕ) (s : ℚ) :
    (W b s : ℝ) = (S b : ℝ) * u s / d b s := by
  apply (eq_div_iff (by exact_mod_cast (d_pos b s).ne')).mpr
  have h : (d b s : ℝ) * W b s = (S b : ℝ) * u s := by exact_mod_cast d_mul_W b s
  nlinarith

theorem normalized_difference (b : ℕ) (s : ℚ) :
    |(U b s : ℝ) - W b s| = (e b s : ℝ) / d b s := by
  have hd : (0 : ℝ) < d b s := by exact_mod_cast d_pos b s
  rw [U_real, W_real, ← sub_div, abs_div, abs_of_pos hd, e_cast]

theorem cross_error (b : ℕ) {s : ℚ} (hs : 1 ≤ s) :
    (e b s : ℝ) = (S b : ℝ) * v s * |(R b : ℝ) - s| := by
  have hS : (0 : ℝ) < S b := by exact_mod_cast S_pos b
  have hv : (0 : ℝ) < v s := by exact_mod_cast v_pos s
  have hid : (P b : ℝ) * v s - (S b : ℝ) * u s =
      ((P b : ℝ) / S b - (u s : ℝ) / v s) * ((S b : ℝ) * v s) := by
    field_simp
  rw [e_cast, hid, abs_mul, abs_of_pos (mul_pos hS hv), R_eq_P_div_S, canonical_real hs]
  ring

theorem localProduct_identity (b : ℕ) {s : ℚ} (hs : 1 ≤ s) :
    localProduct (U b s) (W b s) =
      (e b s : ℝ) * u s / ((P b : ℝ) * smoothPart (u s * v s)) := by
  have hd : (d b s : ℝ) ≠ 0 := by exact_mod_cast (d_pos b s).ne'
  have hP : (P b : ℝ) ≠ 0 := by exact_mod_cast (P_pos b).ne'
  have hS : (S b : ℝ) ≠ 0 := by exact_mod_cast (S_pos b).ne'
  have ht : (smoothPart (u s * v s) : ℝ) ≠ 0 :=
    by exact_mod_cast (smoothPart_pos _).ne'
  have he : (smoothPart (U b s * W b s) : ℝ) =
      (P b : ℝ) * S b * smoothPart (u s * v s) / (d b s : ℝ) ^ 2 := by
    apply (eq_div_iff (pow_ne_zero _ hd)).mpr
    have h : (d b s : ℝ) ^ 2 * smoothPart (U b s * W b s) =
        (P b : ℝ) * S b * smoothPart (u s * v s) := by
      exact_mod_cast smoothPart_normalized_product b hs
    nlinarith
  rw [localProduct, normalized_difference, W_real, he]
  field_simp

theorem localProduct_le_error {b : ℕ} {s : ℚ}
    (hb : 0 < b) (hs1 : 1 ≤ s) (hs2 : s ≤ 2) :
    localProduct (U b s) (W b s) ≤ 2 * (v s : ℝ) ^ 2 * |(R b : ℝ) - s| := by
  have hP : (0 : ℝ) < P b := by exact_mod_cast P_pos b
  have hS : (0 : ℝ) < S b := by exact_mod_cast S_pos b
  have hv : (0 : ℝ) < v s := by exact_mod_cast v_pos s
  have hu : (u s : ℝ) ≤ 2 * v s := by exact_mod_cast u_le_two_v hs1 hs2
  have hSP : (S b : ℝ) ≤ P b := by exact_mod_cast (S_lt_P_lt_two_S hb).1.le
  have ht : (1 : ℝ) ≤ smoothPart (u s * v s) := by
    exact_mod_cast smoothPart_pos (u s * v s)
  have htpos : (0 : ℝ) < smoothPart (u s * v s) := by linarith
  rw [localProduct_identity b hs1, cross_error b hs1]
  apply (div_le_iff₀ (mul_pos hP htpos)).mpr
  have hc : (S b : ℝ) * u s ≤ 2 * v s * (P b * smoothPart (u s * v s)) := by
    have h1 := mul_le_mul_of_nonneg_left hu hS.le
    have h2 := mul_le_mul_of_nonneg_left hSP (by positivity : (0 : ℝ) ≤ 2 * v s)
    have h3 := mul_le_mul_of_nonneg_left ht (by positivity : (0 : ℝ) ≤ 2 * v s * P b)
    nlinarith
  have h := mul_le_mul_of_nonneg_right hc
    (mul_nonneg hv.le (abs_nonneg ((R b : ℝ) - s)))
  nlinarith

theorem normalized_ratio_error (b : ℕ) {s : ℚ} (hs : 1 ≤ s) :
    |(U b s : ℝ) / W b s - 1| = |(R b : ℝ) - s| / (s : ℝ) := by
  have hd : (d b s : ℝ) ≠ 0 := by exact_mod_cast (d_pos b s).ne'
  have hS : (S b : ℝ) ≠ 0 := by exact_mod_cast (S_pos b).ne'
  have hu : (u s : ℝ) ≠ 0 := by exact_mod_cast (u_pos hs).ne'
  have hv : (v s : ℝ) ≠ 0 := by exact_mod_cast (v_pos s).ne'
  have hspos : (0 : ℝ) < s := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hs : (0 : ℚ) < s)
  have hid : (U b s : ℝ) / W b s - 1 = ((R b : ℝ) - s) / (s : ℝ) := by
    rw [U_real, W_real, R_eq_P_div_S, canonical_real hs]
    field_simp
  rw [hid, abs_div, abs_of_pos hspos]

end ErdosMahlerAudit.Gate05
