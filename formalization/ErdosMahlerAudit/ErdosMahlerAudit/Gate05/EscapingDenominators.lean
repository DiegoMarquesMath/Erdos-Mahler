module

public import ErdosMahlerAudit.Gate05.HeightBound

/-! Fixed-exponent logarithmic escape, with the actual Exceptional predicate. -/

public section
namespace ErdosMahlerAudit.Gate05

theorem exceptional_power_bound (hST : SubspaceTwoThreePrimitive)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ b0 : ℕ, 0 < b0 ∧ ∀ b : ℕ, b0 ≤ b → ∀ (ν : ℝ) (s : ℚ),
      Exceptional b ν s → 16 * (s.den : ℝ) ^ (ν - 2) < (3 : ℝ) ^ (ε * (b : ℝ)) := by
  obtain ⟨b0, hb0, hlower⟩ := height_lower hST ε hε
  refine ⟨b0, hb0, ?_⟩
  intro b hb ν s hs
  have hv : (0 : ℝ) < s.den := by exact_mod_cast s.pos
  have hA : (0 : ℝ) < (3 : ℝ) ^ (ε * (b : ℝ)) := by positivity
  have hvν : (0 : ℝ) < (s.den : ℝ) ^ ν := Real.rpow_pos_of_pos hv _
  have h := (hlower b hb s hs.2.2.2.1 hs.2.2.2.2.1 hs.2.2.2.2.2.1).trans_lt
    hs.2.2.2.2.2.2
  have he : (3 : ℝ) ^ (-ε * (b : ℝ)) * (s.den : ℝ) ^ (-2 : ℝ) =
      1 / ((3 : ℝ) ^ (ε * (b : ℝ)) * (s.den : ℝ) ^ 2) := by
    rw [show -ε * (b : ℝ) = -(ε * (b : ℝ)) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_neg hv.le, Real.rpow_two]
    field_simp
  rw [he] at h
  have hc := (one_div_lt_one_div (mul_pos hA (sq_pos_of_pos hv)) (mul_pos (by norm_num) hvν)).mp h
  rw [Real.rpow_sub hv, Real.rpow_two, ← mul_div_assoc]
  exact (div_lt_iff₀ (sq_pos_of_pos hv)).mpr hc

theorem log_bound_of_power_bound {b : ℕ} {s : ℚ} {ν ε : ℝ}
    (h : 16 * (s.den : ℝ) ^ (ν - 2) < (3 : ℝ) ^ (ε * (b : ℝ))) :
    (ν - 2) * Real.log (s.den : ℝ) < ε * (b : ℝ) * Real.log 3 := by
  have hv : (0 : ℝ) < s.den := by exact_mod_cast s.pos
  have hp := Real.rpow_pos_of_pos hv (ν - 2)
  have hl := Real.log_lt_log (mul_pos (by norm_num : (0 : ℝ) < 16) hp) h
  rw [Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) hp.ne',
    Real.log_rpow hv, Real.log_rpow (by norm_num : (0 : ℝ) < 3)] at hl
  have : (0 : ℝ) < Real.log 16 := Real.log_pos (by norm_num)
  linarith

/-- The threshold may depend on fixed ν and η; it is uniform in b and s. -/
theorem exceptional_log_sublinear (hST : SubspaceTwoThreePrimitive)
    (ν : ℝ) (hν : 4 < ν) (_hν5 : ν ≤ 5) :
    ∀ η : ℝ, 0 < η → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → N ∈ convergentDenominators →
      ∀ b : ℕ, N ≤ b → b < 2 * N → ∀ s : ℚ, Exceptional b ν s →
        Real.log (s.den : ℝ) ≤ η * (N : ℝ) := by
  intro η hη
  let ε := η * (ν - 2) / (4 * Real.log 3)
  have hε : 0 < ε := div_pos (mul_pos hη (by linarith)) (mul_pos (by norm_num) log_three_pos)
  obtain ⟨b0, hb0, hpower⟩ := exceptional_power_bound hST hε
  refine ⟨b0, ?_⟩
  intro N hN _ b hb hb2 s hs
  have hlog := log_bound_of_power_bound (hpower b (hN.trans hb) ν s hs)
  have hbR : (b : ℝ) < 2 * (N : ℝ) := by exact_mod_cast hb2
  have hNr : (0 : ℝ) < N := by exact_mod_cast hb0.trans_le hN
  have hscale : ε * (2 * (N : ℝ)) * Real.log 3 = η * (N : ℝ) * (ν - 2) / 2 := by
    dsimp [ε]
    field_simp
    ring
  have hupper : ε * (b : ℝ) * Real.log 3 < η * (N : ℝ) * (ν - 2) / 2 := by
    rw [← hscale]
    exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hbR hε) log_three_pos
  have hgoal : (ν - 2) * Real.log (s.den : ℝ) ≤ (ν - 2) * (η * (N : ℝ)) := by
    have hp : 0 < η * (N : ℝ) * (ν - 2) := mul_pos (mul_pos hη hNr) (by linarith)
    nlinarith
  exact (mul_le_mul_iff_right₀ (by linarith : 0 < ν - 2)).mp hgoal

end ErdosMahlerAudit.Gate05
