module

public import ErdosMahlerAudit.Gate06.Separation

/-! Exact strict errors with constants 1/4 and 1/2, TeX 719–733. -/

public section
namespace ErdosMahlerAudit.Gate06

theorem exceptional_error_at_cutoff {b : ℕ} {ν B : ℝ} {s : ℚ}
    (hs : Exceptional b ν s) (hB : 0 < B) (hd : B < (s.den : ℝ)) :
    |(s : ℝ) - (R b : ℝ)| < (1 / 16 : ℝ) * B ^ (-ν) := by
  have hs0 : (0 : ℝ) < s.den := by exact_mod_cast s.pos
  have he : 1 / (16 * (s.den : ℝ) ^ ν) = (1 / 16 : ℝ) * (s.den : ℝ) ^ (-ν) := by
    rw [Real.rpow_neg hs0.le]
    ring
  have hm := Real.rpow_le_rpow_of_nonpos hB hd.le (by linarith [hs.2.1] : -ν ≤ 0)
  rw [abs_sub_comm]
  exact hs.2.2.2.2.2.2.trans_le (he ▸ mul_le_mul_of_nonneg_left hm (by norm_num))

/-- A real product estimate isolated from witness selection. -/
theorem product_error_bound {x y u v ε : ℝ}
    (hy : |y| ≤ 2) (hu : |u| ≤ 2)
    (hx : |x - u| < ε) (hv : |y - v| < ε) :
    |x * y - u * v| < 4 * ε := by
  have hid : x * y - u * v = (x - u) * y + u * (y - v) := by ring
  calc
    _ ≤ |x - u| * |y| + |u| * |y - v| := by
      rw [hid]
      simpa only [abs_mul] using abs_add_le ((x - u) * y) (u * (y - v))
    _ ≤ |x - u| * 2 + 2 * |y - v| := add_le_add
      (mul_le_mul_of_nonneg_left hy (abs_nonneg _))
      (mul_le_mul_of_nonneg_right hu (abs_nonneg _))
    _ < _ := by linarith

theorem exceptional_product_error {b c : ℕ} {ν B : ℝ} {s t : ℚ}
    (hs : Exceptional b ν s) (ht : Exceptional c ν t)
    (hB : 0 < B) (hsd : B < (s.den : ℝ)) (htd : B < (t.den : ℝ)) :
    |((s * t : ℚ) : ℝ) - ((R b * R c : ℚ) : ℝ)| < (1 / 4 : ℝ) * B ^ (-ν) := by
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht.2.2.2.1
  have ht2 : (t : ℝ) ≤ 2 := by exact_mod_cast ht.2.2.2.2.1
  have hR := R_mem_Ioo hs.1
  have h := product_error_bound
    (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ t)]; exact ht2)
    (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ R b)]; exact hR.2.le)
    (exceptional_error_at_cutoff hs hB hsd) (exceptional_error_at_cutoff ht hB htd)
  simpa only [Rat.cast_mul, show (4 : ℝ) * (1 / 16) = 1 / 4 by norm_num, ← mul_assoc] using h

theorem selected_product_error {N b c : ℕ} {ν θ w : ℝ}
    (hb : b ∈ exceptionalBand N ν θ w) (hc : c ∈ exceptionalBand N ν θ w) :
    |((selectedFraction N ν θ w b * selectedFraction N ν θ w c : ℚ) : ℝ) -
      ((R b * R c : ℚ) : ℝ)| < (1 / 4 : ℝ) * V θ w ^ (-ν) := by
  have hs := selectedFraction_spec hb
  have ht := selectedFraction_spec hc
  exact exceptional_product_error hs.1 ht.1 (V_pos θ w)
    ((le_max_left _ _).trans_lt hs.2.1) ((le_max_left _ _).trans_lt ht.2.1)

theorem equal_prescribed_products_error {N b c b' c' : ℕ} {ν θ w : ℝ}
    (hb : b ∈ exceptionalBand N ν θ w) (hc : c ∈ exceptionalBand N ν θ w)
    (hb' : b' ∈ exceptionalBand N ν θ w) (hc' : c' ∈ exceptionalBand N ν θ w)
    (he : R b * R c = R b' * R c') :
    |((selectedFraction N ν θ w b * selectedFraction N ν θ w c : ℚ) : ℝ) -
      ((selectedFraction N ν θ w b' * selectedFraction N ν θ w c' : ℚ) : ℝ)| <
        (1 / 2 : ℝ) * V θ w ^ (-ν) := by
  have h1 := selected_product_error hb hc
  have h2 := selected_product_error hb' hc'
  rw [← he, abs_sub_comm] at h2
  have htri := abs_sub_le
    ((selectedFraction N ν θ w b * selectedFraction N ν θ w c : ℚ) : ℝ)
    ((R b * R c : ℚ) : ℝ)
    ((selectedFraction N ν θ w b' * selectedFraction N ν θ w c' : ℚ) : ℝ)
  linarith

end ErdosMahlerAudit.Gate06
