module

public import ErdosMahlerAudit.Gate03.Rotation

/-! Clipped closed exceptional neighborhoods and multiplicity, TeX 505–511. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate04

noncomputable def exceptionalRadius (s : ℚ) (ν : ℝ) : ℝ :=
  1 / (16 * (s.den : ℝ) ^ ν)

noncomputable def clippedLower (s : ℚ) (ν : ℝ) : ℝ :=
  max 1 ((s : ℝ) - exceptionalRadius s ν)

noncomputable def clippedUpper (s : ℚ) (ν : ℝ) : ℝ :=
  min 2 ((s : ℝ) + exceptionalRadius s ν)

noncomputable def witnessIndices (N : ℕ) (ν : ℝ) (s : ℚ) : Finset ℕ := by
  classical
  exact (Finset.Ico N (2 * N)).filter (fun b => Exceptional b ν s)

theorem exceptionalRadius_pos (s : ℚ) (ν : ℝ) : 0 < exceptionalRadius s ν := by
  have hd : (0 : ℝ) < s.den := by exact_mod_cast s.pos
  exact div_pos zero_lt_one (mul_pos (by norm_num) (Real.rpow_pos_of_pos hd ν))

/-- Elementary logarithmic distortion; in particular Phi is decreasing and
2-Lipschitz on [1,2]. The estimate is valid on the larger domain [1,∞). -/
theorem Phi_difference_bounds {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    0 ≤ Phi x - Phi y ∧ Phi x - Phi y ≤ 2 * (y - x) := by
  have hxpos : 0 < x := by linarith
  have hypos : 0 < y := by linarith
  have hlognonneg := (Real.log_le_log_iff hxpos hypos).mpr hxy
  have hlog := Real.log_le_sub_one_of_pos (div_pos hypos hxpos)
  rw [Real.log_div hypos.ne' hxpos.ne'] at hlog
  have hratio : y / x - 1 ≤ y - x := by
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hxpos).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hxy)]
  have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hdiff : Phi x - Phi y = (Real.log y - Real.log x) / Real.log 2 := by
    unfold Phi
    ring
  rw [hdiff]
  constructor
  · exact div_nonneg (sub_nonneg.mpr hlognonneg) log_two_pos.le
  · apply (div_le_iff₀ log_two_pos).mpr
    have hlogbound : Real.log y - Real.log x ≤ y - x := hlog.trans hratio
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (by linarith : 0 ≤ 2 * Real.log 2 - 1)]

theorem clipped_bounds {s : ℚ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (ν : ℝ) :
    1 ≤ clippedLower s ν ∧ clippedLower s ν ≤ clippedUpper s ν ∧
      clippedUpper s ν ≤ 2 := by
  have h1 : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have h2 : (s : ℝ) ≤ 2 := by exact_mod_cast hs2
  have hr := exceptionalRadius_pos s ν
  refine ⟨le_max_left _ _, ?_, min_le_left _ _⟩
  exact le_trans (max_le h1 (by linarith)) (le_min h2 (by linarith))

theorem exceptional_mem_clipped {b : ℕ} {ν : ℝ} {s : ℚ}
    (h : Exceptional b ν s) :
    (R b : ℝ) ∈ Set.Icc (clippedLower s ν) (clippedUpper s ν) := by
  have hR := R_mem_Ioo h.1
  have herr := abs_lt.mp h.2.2.2.2.2.2
  exact ⟨max_le hR.1.le (by dsimp [exceptionalRadius] at *; linarith),
    le_min hR.2.le (by dsimp [exceptionalRadius] at *; linarith)⟩

/-- Closed endpoints are retained after reversing the decreasing map. -/
theorem exceptional_fract_mem_closed {b : ℕ} {ν : ℝ} {s : ℚ}
    (h : Exceptional b ν s) :
    Int.fract ((b : ℝ) * alpha) ∈
      Set.Icc (Phi (clippedUpper s ν)) (Phi (clippedLower s ν)) := by
  have hc := exceptional_mem_clipped h
  have hb := clipped_bounds h.2.2.2.1 h.2.2.2.2.1 ν
  have hlo := (Phi_difference_bounds hb.1 hc.1).1
  have hhi := (Phi_difference_bounds (R_mem_Ioo h.1).1.le hc.2).1
  rw [Phi_R h.1] at hlo hhi
  exact ⟨by linarith, by linarith⟩

/-- An absolute length estimate, with canonical positive denominator. -/
theorem clipped_image_length {s : ℚ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (ν : ℝ) :
    0 ≤ Phi (clippedLower s ν) - Phi (clippedUpper s ν) ∧
      Phi (clippedLower s ν) - Phi (clippedUpper s ν) ≤ (s.den : ℝ) ^ (-ν) := by
  have hb := clipped_bounds hs1 hs2 ν
  obtain ⟨h0, hlen⟩ := Phi_difference_bounds hb.1 hb.2.1
  have hl := le_max_right 1 ((s : ℝ) - exceptionalRadius s ν)
  have hu := min_le_right 2 ((s : ℝ) + exceptionalRadius s ν)
  have hwidth : Phi (clippedLower s ν) - Phi (clippedUpper s ν) ≤
      4 * exceptionalRadius s ν := by
    change _ ≤ clippedLower s ν at hl
    change clippedUpper s ν ≤ _ at hu
    linarith
  have hd : (0 : ℝ) < s.den := by exact_mod_cast s.pos
  have hp := Real.rpow_pos_of_pos hd ν
  refine ⟨h0, hwidth.trans ?_⟩
  rw [Real.rpow_neg hd.le]
  unfold exceptionalRadius
  have he : 4 * (1 / (16 * (s.den : ℝ) ^ ν)) = ((s.den : ℝ) ^ ν)⁻¹ / 4 := by
    field_simp
    ring
  rw [he]
  have : 0 < ((s.den : ℝ) ^ ν)⁻¹ := inv_pos.mpr hp
  linarith

/-- Every fixed rational witness is counted using the arbitrary closed-interval
rotation bound, with no special-parent interval hypothesis. -/
theorem witnessIndices_card_le {N : ℕ} (hN : N ∈ convergentDenominators)
    {s : ℚ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (ν : ℝ) :
    ((witnessIndices N ν s).card : ℝ) ≤ (N : ℝ) * (s.den : ℝ) ^ (-ν) + 3 := by
  classical
  obtain ⟨hlen0, hlen⟩ := clipped_image_length hs1 hs2 ν
  have h := Gate03.rotation_closed_upper hN (witnessIndices N ν s)
    (Finset.filter_subset _ _) (Phi (clippedUpper s ν)) (Phi (clippedLower s ν))
    (by linarith) (fun b hb => exceptional_fract_mem_closed (Finset.mem_filter.mp hb).2)
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_left hlen (Nat.cast_nonneg N)) le_rfl)

/-- Uniform shell version; no coefficient depends on the exponent or rational. -/
theorem witnessIndices_card_le_shell {N : ℕ} (hN : N ∈ convergentDenominators)
    {s : ℚ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) {ν V : ℝ}
    (hν : 0 ≤ ν) (hV : 0 < V) (hv : V < (s.den : ℝ)) :
    ((witnessIndices N ν s).card : ℝ) ≤ (N : ℝ) * V ^ (-ν) + 3 := by
  exact (witnessIndices_card_le hN hs1 hs2 ν).trans
    (add_le_add (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hV hv.le (neg_nonpos.mpr hν)) (Nat.cast_nonneg N)) le_rfl)

end ErdosMahlerAudit.Gate04
