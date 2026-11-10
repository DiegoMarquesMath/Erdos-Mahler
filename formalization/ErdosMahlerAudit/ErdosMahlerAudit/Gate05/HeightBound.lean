module

public import ErdosMahlerAudit.Gate05.FinitePairs

/-! Lemma 3.2's height estimate, conditional only on the precise external input. -/

public section
namespace ErdosMahlerAudit.Gate05

theorem S_rpow (b : ℕ) (t : ℝ) : (S b : ℝ) ^ t = (3 : ℝ) ^ (t * (b : ℝ)) := by
  simp only [S, Nat.cast_pow, Nat.cast_ofNat]
  rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

theorem eventually_S_neg_lt {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ) :
    ∃ B : ℕ, ∀ b : ℕ, B ≤ b → (S b : ℝ) ^ (-ε) < γ := by
  have hbase : (1 : ℝ) < (3 : ℝ) ^ ε := by
    simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 3) hε
  obtain ⟨B, hB⟩ := pow_unbounded_of_one_lt (1 / γ) hbase
  refine ⟨B, ?_⟩
  intro b hb
  have hlarge := hB.trans_le (pow_le_pow_right₀ hbase.le hb)
  have h := one_div_lt_one_div_of_lt (div_pos zero_lt_one hγ) hlarge
  have hid : (S b : ℝ) ^ (-ε) = (((3 : ℝ) ^ ε) ^ b)⁻¹ := by
    rw [Real.rpow_neg (by exact_mod_cast (S_pos b).le), S_rpow,
      Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
  simpa only [hid, one_div, inv_inv] using h

theorem height_lower_S (hST : SubspaceTwoThreePrimitive) {ε : ℝ} (hε : 0 < ε) :
    ∃ b0 : ℕ, 0 < b0 ∧ ∀ b : ℕ, b0 ≤ b → ∀ s : ℚ,
      1 ≤ s → s ≤ 2 → s ≠ R b →
        (S b : ℝ) ^ (-ε) * (v s : ℝ) ^ (-2 : ℝ) ≤ |(R b : ℝ) - s| := by
  obtain ⟨γ, hγ, hgap⟩ := finite_pair_gap (smallProductPairs ε) (smallProductPairs_finite hST hε)
  obtain ⟨B, hB⟩ := eventually_S_neg_lt hε hγ
  refine ⟨max 1 B, lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _), ?_⟩
  intro b hb s hs1 hs2 hne
  have hbpos : 0 < b := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans hb)
  by_contra h
  have herr := lt_of_not_ge h
  have hmem := violating_pair_mem hbpos hs1 hs2 hε hne herr
  have hg := hgap (U b s, W b s) hmem (W_pos b hs1) (U_ne_W hs1 hne)
  rw [normalized_ratio_error b hs1] at hg
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hr : |(R b : ℝ) - s| / (s : ℝ) ≤ |(R b : ℝ) - s| :=
    div_le_self (abs_nonneg _) hsR
  have hv : (1 : ℝ) ≤ v s := by exact_mod_cast v_pos s
  have hp : (v s : ℝ) ^ (-2 : ℝ) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hv (by norm_num : (-2 : ℝ) ≤ 0)
  have hsmall : (S b : ℝ) ^ (-ε) * (v s : ℝ) ^ (-2 : ℝ) ≤ (S b : ℝ) ^ (-ε) := by
    have hS : (0 : ℝ) < S b := by exact_mod_cast S_pos b
    simpa using mul_le_mul_of_nonneg_left hp (Real.rpow_pos_of_pos hS (-ε)).le
  exact (not_lt_of_ge (hg.trans hr))
    (herr.trans_le hsmall |>.trans (hB b ((le_max_right _ _).trans hb)))

/-- b0 precedes both the index and every canonical rational witness. -/
theorem height_lower (hST : SubspaceTwoThreePrimitive) :
    ∀ ε : ℝ, 0 < ε → ∃ b0 : ℕ, 0 < b0 ∧ ∀ b : ℕ, b0 ≤ b → ∀ s : ℚ,
      1 ≤ s → s ≤ 2 → s ≠ R b →
        (3 : ℝ) ^ (-ε * (b : ℝ)) * (s.den : ℝ) ^ (-2 : ℝ) ≤ |(R b : ℝ) - s| := by
  intro ε hε
  simpa only [S_rpow, v] using height_lower_S hST hε

end ErdosMahlerAudit.Gate05
