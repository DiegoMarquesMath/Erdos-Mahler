module

public import ErdosMahlerAudit.Gate08.Selection

/-! The actual logarithmic form and strict approximation error, TeX 848–865. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate08
open Gate06

/-- Coefficients are signed differences, never truncated natural subtraction. -/
noncomputable def linearForm (b c q : ℕ) (g : ℚ) : ℝ :=
  ((a c : ℝ) - (a b : ℝ)) * Real.log 2 -
    ((c : ℝ) - (b : ℝ)) * Real.log 3 - (q : ℝ) * Real.log (g : ℝ)

theorem log_lipschitz_one {u v : ℝ} (hu : 1 ≤ u) (hv : 1 ≤ v) :
    |Real.log u - Real.log v| ≤ |u - v| := by
  have step {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
      Real.log y - Real.log x ≤ y - x := by
    have hx0 : 0 < x := by linarith
    have hy0 : 0 < y := by linarith
    have hh := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
    rw [Real.log_div hy0.ne' hx0.ne'] at hh
    have hr : y / x - 1 ≤ y - x := by
      apply (sub_le_iff_le_add).mpr
      apply (div_le_iff₀ hx0).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hxy)]
    exact hh.trans hr
  rcases le_total u v with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log (by linarith) h)),
      abs_of_nonpos (sub_nonpos.mpr h)]
    linarith [step hu h]
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log (by linarith) h)),
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact step hv h

theorem selected_log_error {N b : ℕ} {ν θ w : ℝ}
    (hb : b ∈ exceptionalBand N ν θ w) :
    |Real.log (R b : ℝ) - Real.log (selectedFraction N ν θ w b : ℝ)| <
      (1 / 16 : ℝ) * Real.exp (-ν * w / θ) := by
  have hs := selectedFraction_spec hb
  have hsr : (1 : ℝ) ≤ selectedFraction N ν θ w b := by
    exact_mod_cast hs.1.2.2.2.1
  have hl := log_lipschitz_one (R_mem_Ioo hs.1.1).1.le hsr
  have he := exceptional_error_at_cutoff hs.1 (V_pos θ w)
    ((le_max_left _ _).trans_lt hs.2.1)
  rw [abs_sub_comm] at he
  have hp : V θ w ^ (-ν) = Real.exp (-ν * w / θ) := by
    rw [V, ← Real.exp_mul]
    congr 1
    ring
  rw [hp] at he
  exact hl.trans_lt he

theorem linearForm_identity {b c q : ℕ} {s t g : ℚ}
    (hs : 0 < s) (ht : 0 < t) (hg : 0 < g) (he : t / s = g ^ q) :
    linearForm b c q g =
      Real.log ((R c : ℝ) / (t : ℝ)) - Real.log ((R b : ℝ) / (s : ℝ)) := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg
  have hb0 : (0 : ℝ) < R b := by exact_mod_cast R_pos b
  have hc0 : (0 : ℝ) < R c := by exact_mod_cast R_pos c
  have hr : (t : ℝ) / (s : ℝ) = (g : ℝ) ^ q := by exact_mod_cast he
  have hl := congrArg Real.log hr
  rw [Real.log_div ht0.ne' hs0.ne', Real.log_pow] at hl
  rw [Real.log_div hc0.ne' ht0.ne', Real.log_div hb0.ne' hs0.ne', log_R, log_R]
  have ha : alpha * Real.log 2 = Real.log 3 := by
    exact div_mul_cancel₀ _ log_two_pos.ne'
  dsimp [linearForm]
  nlinarith [hl, ha]

theorem selected_linearForm_small {N b c q : ℕ} {ν θ w : ℝ} {g : ℚ}
    (hb : b ∈ exceptionalBand N ν θ w) (hc : c ∈ exceptionalBand N ν θ w)
    (hg : 0 < g)
    (he : selectedFraction N ν θ w c / selectedFraction N ν θ w b = g ^ q) :
    |linearForm b c q g| < (1 / 8 : ℝ) * Real.exp (-ν * w / θ) := by
  have hs := selectedFraction_spec hb
  have ht := selectedFraction_spec hc
  have hs0 : (0 : ℚ) < selectedFraction N ν θ w b := by linarith [hs.1.2.2.2.1]
  have ht0 : (0 : ℚ) < selectedFraction N ν θ w c := by linarith [ht.1.2.2.2.1]
  have hsR : (0 : ℝ) < selectedFraction N ν θ w b := by exact_mod_cast hs0
  have htR : (0 : ℝ) < selectedFraction N ν θ w c := by exact_mod_cast ht0
  have hbR : (0 : ℝ) < R b := by exact_mod_cast R_pos b
  have hcR : (0 : ℝ) < R c := by exact_mod_cast R_pos c
  rw [linearForm_identity hs0 ht0 hg he,
    Real.log_div hcR.ne' htR.ne', Real.log_div hbR.ne' hsR.ne']
  have h1 := selected_log_error hb
  have h2 := selected_log_error hc
  calc
    _ ≤ |Real.log (R c : ℝ) - Real.log (selectedFraction N ν θ w c : ℝ)| +
        |Real.log (R b : ℝ) - Real.log (selectedFraction N ν θ w b : ℝ)| := abs_sub _ _
    _ < _ := by linarith

/-- An algebraic/logarithmic bridge only: it does not assert that the form vanishes. -/
theorem ratio_eq_of_linearForm_zero {b c q : ℕ} {s t g : ℚ}
    (hs : 0 < s) (ht : 0 < t) (hg : 0 < g) (he : t / s = g ^ q)
    (hz : linearForm b c q g = 0) : t / s = R c / R b := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hb0 : (0 : ℝ) < R b := by exact_mod_cast R_pos b
  have hc0 : (0 : ℝ) < R c := by exact_mod_cast R_pos c
  rw [linearForm_identity hs ht hg he, sub_eq_zero] at hz
  have hh := Real.log_injOn_pos (div_pos hc0 ht0) (div_pos hb0 hs0) hz
  have hr : (t : ℝ) / s = (R c : ℝ) / (R b : ℝ) := by
    apply (div_eq_div_iff hs0.ne' hb0.ne').mpr
    have hcross := (div_eq_div_iff ht0.ne' hs0.ne').mp hh
    nlinarith
  exact_mod_cast hr

end ErdosMahlerAudit.Gate08
