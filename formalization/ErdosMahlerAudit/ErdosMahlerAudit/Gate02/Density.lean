module

public import ErdosMahlerAudit.Gate02.FiniteCounting

/-! Elementary interval and density estimates for the actual Phi and R. -/

public section

namespace ErdosMahlerAudit.Gate02

/-- This identifies the interval whose endpoint difference defines rho;
rho is not a free density parameter or a surrogate for the image length. -/
theorem Phi_image_J (t : ℕ) (τ : ℝ) :
    Phi '' J t τ =
      Set.Ioo (Phi ((R t : ℝ) + 2 * radius t τ))
        (Phi ((R t : ℝ) + radius t τ)) := by
  have hR : (0 : ℝ) < R t := by exact_mod_cast R_pos t
  have hr := radius_pos t τ
  have hpos : ∀ x ∈ Set.Icc ((R t : ℝ) + radius t τ)
      ((R t : ℝ) + 2 * radius t τ), 0 < x := by
    intro x hx
    have := hx.1
    linarith
  apply ContinuousOn.image_Ioo_of_strictAntiOn (by linarith)
  · intro x hx
    exact continuousWithinAt_const.sub
      ((Real.continuousAt_log (ne_of_gt (hpos x hx))).continuousWithinAt.div_const _)
  · intro x hx y _ hxy
    exact sub_lt_sub_left
      ((div_lt_div_iff_of_pos_right log_two_pos).mpr (Real.log_lt_log (hpos x hx) hxy)) 1

theorem rho_pos (t : ℕ) (τ : ℝ) : 0 < rho t τ := by
  have hR : (0 : ℝ) < R t := by exact_mod_cast R_pos t
  have hr := radius_pos t τ
  have hlog := Real.log_lt_log (by linarith : 0 < (R t : ℝ) + radius t τ)
    (by linarith : (R t : ℝ) + radius t τ < (R t : ℝ) + 2 * radius t τ)
  have hdiv := (div_lt_div_iff_of_pos_right log_two_pos).mpr hlog
  dsimp [rho, Phi]
  linarith

theorem R_le_two_sub_inv {t : ℕ} (ht : 0 < t) :
    (R t : ℝ) ≤ 2 - 1 / (3 : ℝ) ^ t := by
  have hQ : (0 : ℝ) < (3 : ℝ) ^ t := by positivity
  have hlt := (R_mem_Ioo ht).2
  rw [R_cast, div_lt_iff₀ hQ] at hlt
  have hn : (2 : ℕ) ^ a t < 2 * 3 ^ t := by exact_mod_cast hlt
  have hn' : (2 : ℝ) ^ a t + 1 ≤ 2 * (3 : ℝ) ^ t := by
    exact_mod_cast (Nat.add_one_le_iff.mpr hn)
  rw [R_cast, div_le_iff₀ hQ]
  field_simp
  nlinarith

theorem three_le_Q {t : ℕ} (ht : 0 < t) : (3 : ℝ) ≤ (3 : ℝ) ^ t := by
  simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) ht)

theorem interval_upper {t : ℕ} {τ : ℝ} (ht : 0 < t) (hτ : 4 ≤ τ) :
    (R t : ℝ) + 2 * radius t τ < 2 := by
  have hQ := three_le_Q ht
  have hQpos : (0 : ℝ) < (3 : ℝ) ^ t := by positivity
  have hr : radius t τ ≤ 1 / ((3 : ℝ) ^ t) ^ 2 := by
    rw [radius_eq_Q]
    have h := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ 3 ^ t)
      (by linarith : -τ ≤ -(2 : ℝ))
    simpa only [Real.rpow_neg hQpos.le, Real.rpow_two, one_div] using h
  have hsmall : 2 / ((3 : ℝ) ^ t) ^ 2 < 1 / (3 : ℝ) ^ t := by
    apply (div_lt_div_iff₀ (sq_pos_of_pos hQpos) hQpos).mpr
    nlinarith
  have hR := R_le_two_sub_inv ht
  simp only [div_eq_mul_inv] at hr hsmall hR
  linarith

theorem J_subset_Ioo {t : ℕ} {τ : ℝ} (ht : 0 < t) (hτ : 4 ≤ τ) :
    J t τ ⊆ Set.Ioo 1 2 := by
  intro y hy
  have hR := (R_mem_Ioo ht).1
  have hr := radius_pos t τ
  have hu := interval_upper ht hτ
  exact ⟨by have := hy.1; linarith, hy.2.trans hu⟩

theorem cutoff_ge_two {t : ℕ} {τ : ℝ} (ht : 0 < t) (hτ : 4 ≤ τ) :
    2 ≤ cutoff t τ := by
  have hQ := three_le_Q ht
  have hpow := Real.rpow_le_rpow_of_exponent_le
    (by linarith : (1 : ℝ) ≤ 3 ^ t) (by linarith : (3 : ℝ) ≤ τ - 1)
  have hcube : (27 : ℝ) ≤ ((3 : ℝ) ^ t) ^ 3 := by
    nlinarith [sq_nonneg ((3 : ℝ) ^ t - 3)]
  norm_num only [Real.rpow_ofNat] at hpow
  dsimp [cutoff]
  linarith

/-- A logarithmic inequality proves the manuscript's lower distortion bound
directly, without assuming a derivative or a mean-value theorem conclusion. -/
theorem rho_lower {t : ℕ} {τ : ℝ} (hupper : (R t : ℝ) + 2 * radius t τ ≤ 2) :
    radius t τ / (2 * Real.log 2) ≤ rho t τ := by
  let x := (R t : ℝ) + radius t τ
  let y := (R t : ℝ) + 2 * radius t τ
  have hR : (0 : ℝ) < R t := by exact_mod_cast R_pos t
  have hr := radius_pos t τ
  have hx : 0 < x := by dsimp [x]; linarith
  have hy : 0 < y := by dsimp [y]; linarith
  have hxy : y - x = radius t τ := by dsimp [x, y]; ring
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hy hx)
  rw [Real.log_div (ne_of_gt hy) (ne_of_gt hx), inv_div] at hlog
  have hratio : (y - x) / y ≤ Real.log y - Real.log x := by
    calc
      (y - x) / y = 1 - x / y := by field_simp
      _ ≤ _ := hlog
  have hhalf : radius t τ / 2 ≤ (y - x) / y := by
    rw [hxy]
    exact div_le_div_of_nonneg_left hr.le hy hupper
  have h := hhalf.trans hratio
  dsimp [rho, Phi]
  change radius t τ / (2 * Real.log 2) ≤
    (1 - Real.log x / Real.log 2) - (1 - Real.log y / Real.log 2)
  apply (div_le_iff₀ (mul_pos (by norm_num) log_two_pos)).mpr
  field_simp
  linarith

theorem exceptional_density_upper {t : ℕ} {τ C : ℝ}
    (ht : 0 < t) (hτ : 4 ≤ τ) (hC : 0 ≤ C) :
    C * (cutoff t τ) ^ (2 - nu t) ≤
      36 * C * radius t τ / ((3 : ℝ) ^ t) ^ 2 := by
  have hQ := three_le_Q ht
  have hQpos : (0 : ℝ) < (3 : ℝ) ^ t := by positivity
  have hD := cutoff_ge_two ht hτ
  have hν := (parent_parameters ht τ).2.1
  have hpow := Real.rpow_le_rpow_of_exponent_le
    (by linarith : 1 ≤ cutoff t τ) (by linarith : 2 - nu t ≤ -(2 : ℝ))
  have heq : (cutoff t τ) ^ (-(2 : ℝ)) =
      36 * radius t τ * ((3 : ℝ) ^ t) ^ (2 - τ) := by
    rw [cutoff, Real.div_rpow (le_of_lt (Real.rpow_pos_of_pos hQpos _))
      (by norm_num : (0 : ℝ) ≤ 6), ← Real.rpow_mul hQpos.le, radius_eq_Q]
    have hexp : (τ - 1) * -(2 : ℝ) = -τ + (2 - τ) := by ring
    rw [hexp, Real.rpow_add hQpos]
    norm_num [Real.rpow_neg]
    ring
  have hsmall : ((3 : ℝ) ^ t) ^ (2 - τ) ≤ 1 / ((3 : ℝ) ^ t) ^ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ 3 ^ t)
      (by linarith : 2 - τ ≤ -(2 : ℝ))
    simpa only [Real.rpow_neg hQpos.le, Real.rpow_two, one_div] using h
  calc
    C * (cutoff t τ) ^ (2 - nu t) ≤ C * (cutoff t τ) ^ (-(2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hpow hC
    _ = 36 * C * radius t τ * ((3 : ℝ) ^ t) ^ (2 - τ) := by rw [heq]; ring
    _ ≤ 36 * C * radius t τ * (1 / ((3 : ℝ) ^ t) ^ 2) :=
      mul_le_mul_of_nonneg_left hsmall
        (mul_nonneg (mul_nonneg (by norm_num) hC) (radius_pos t τ).le)
    _ = _ := by ring

/-- Includes τ=4. A single threshold depending on C works for every τ≥4. -/
theorem eventually_density_gap (C : ℝ) (hC : 0 < C) :
    ∃ t0 : ℕ, 0 < t0 ∧ ∀ t : ℕ, t0 ≤ t → ∀ τ : ℝ, 4 ≤ τ →
      C * (cutoff t τ) ^ (2 - nu t) < rho t τ := by
  obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt (72 * C * Real.log 2)
    (by norm_num : (1 : ℝ) < 3)
  refine ⟨M + 1, Nat.succ_pos _, ?_⟩
  intro t ht τ hτ
  have htpos : 0 < t := lt_of_lt_of_le (Nat.succ_pos M) ht
  have hMt : M ≤ t := (Nat.le_succ M).trans ht
  have hQ := three_le_Q htpos
  have hQt : (72 * C * Real.log 2) < (3 : ℝ) ^ t :=
    hM.trans_le (pow_le_pow_right₀ (by norm_num) hMt)
  have hQsq : 72 * C * Real.log 2 < ((3 : ℝ) ^ t) ^ 2 := by nlinarith
  have hr := radius_pos t τ
  have hstrict : 36 * C * radius t τ / ((3 : ℝ) ^ t) ^ 2 <
      radius t τ / (2 * Real.log 2) := by
    apply (div_lt_div_iff₀ (by positivity) (mul_pos (by norm_num) log_two_pos)).mpr
    nlinarith [mul_lt_mul_of_pos_right hQsq hr]
  exact (exceptional_density_upper htpos hτ hC.le).trans_lt
    (hstrict.trans_le (rho_lower (interval_upper htpos hτ).le))

end ErdosMahlerAudit.Gate02
