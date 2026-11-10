module

public import ErdosMahlerAudit.Gate06.Band

/-! Positive real cutoffs and canonical reduced-product separation, TeX 734–740. -/

public section
namespace ErdosMahlerAudit.Gate06

theorem V_pos (θ w : ℝ) : 0 < V θ w := Real.exp_pos _
theorem H_pos (w : ℝ) : 0 < H w := Real.exp_pos _

theorem V_gt_one {θ w : ℝ} (hθ : 1 < θ) (hw : 0 < w) : 1 < V θ w := by
  exact Real.one_lt_exp_iff.mpr (div_pos hw (by linarith))

theorem H_eq_V_rpow {θ w : ℝ} (hθ : 1 < θ) : H w = V θ w ^ θ := by
  rw [H, V, ← Real.exp_mul, div_mul_cancel₀ w (by linarith : θ ≠ 0)]

theorem product_den_le (r s : ℚ) : (r * s).den ≤ r.den * s.den :=
  Nat.le_of_dvd (Nat.mul_pos r.pos s.pos) (Rat.mul_den_dvd r s)

theorem product_den_le_square {r s : ℚ} {B : ℝ}
    (hr : (r.den : ℝ) ≤ B) (hs : (s.den : ℝ) ≤ B) :
    ((r * s).den : ℝ) ≤ B ^ 2 := by
  have hr0 : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hs0 : (0 : ℝ) < s.den := by exact_mod_cast s.pos
  have hden : ((r * s).den : ℝ) ≤ (r.den : ℝ) * (s.den : ℝ) := by
    exact_mod_cast product_den_le r s
  exact hden.trans (by nlinarith [mul_le_mul hr hs hs0.le (hr0.le.trans hr)])

theorem bounded_product_separation {r s : ℚ} {B : ℝ} (hB : 0 < B)
    (hr : (r.den : ℝ) ≤ B ^ 2) (hs : (s.den : ℝ) ≤ B ^ 2) (hne : r ≠ s) :
    B ^ (-4 : ℝ) ≤ |(r : ℝ) - (s : ℝ)| := by
  have hr0 : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hs0 : (0 : ℝ) < s.den := by exact_mod_cast s.pos
  have hp : (r.den : ℝ) * (s.den : ℝ) ≤ B ^ 4 := by
    calc
      _ ≤ B ^ 2 * B ^ 2 := mul_le_mul hr hs hs0.le (sq_nonneg B)
      _ = _ := by ring
  have he : B ^ (-4 : ℝ) = 1 / B ^ (4 : ℕ) := by
    rw [Real.rpow_neg hB.le]
    norm_num [one_div]
  rw [he]
  exact (one_div_le_one_div_of_le (mul_pos hr0 hs0) hp).trans (rational_separation hne)

theorem power_gap {ν θ w : ℝ} (hθ : 1 < θ) (hθν : θ < ν / 4) (hw : 0 < w) :
    V θ w ^ (-ν) < H w ^ (-4 : ℝ) := by
  rw [H_eq_V_rpow hθ, ← Real.rpow_mul (V_pos θ w).le]
  exact Real.rpow_lt_rpow_of_exponent_lt (V_gt_one hθ hw) (by linarith)

theorem half_power_gap {ν θ w : ℝ} (hθ : 1 < θ) (hθν : θ < ν / 4) (hw : 0 < w) :
    (1 / 2 : ℝ) * V θ w ^ (-ν) < H w ^ (-4 : ℝ) := by
  have hg := power_gap hθ hθν hw
  have hp := Real.rpow_pos_of_pos (V_pos θ w) (-ν)
  linarith

end ErdosMahlerAudit.Gate06
