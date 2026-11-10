module

public import ErdosMahlerAudit.Definitions

/-!
# Gate 01: elementary arithmetic of the prescribed fractions

These proofs cover `source/Erdos_Mahler.tex:138–151` and the rational
separation and elementary denominator bound at lines 538–544. No counting
proposition, asymptotic height bound, or external Diophantine theorem is assumed.
-/

public section

namespace ErdosMahlerAudit

@[simp] theorem a_zero : a 0 = 0 := by simp [a]

@[simp] theorem R_zero : R 0 = 1 := by simp [R]

@[simp] theorem Phi_one : Phi 1 = 1 := by simp [Phi]

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem log_three_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)

theorem alpha_pos : 0 < alpha := div_pos log_three_pos log_two_pos

/-- Unique factorization, in the form that 3 cannot divide a power of 2. -/
theorem mul_log_three_ne_mul_log_two {b : ℕ} (hb : 0 < b) (n : ℕ) :
    (b : ℝ) * Real.log 3 ≠ (n : ℝ) * Real.log 2 := by
  intro h
  have he : (3 : ℝ) ^ b = (2 : ℝ) ^ n := by
    apply Real.log_injOn_pos (by change 0 < (3 : ℝ) ^ b; positivity)
      (by change 0 < (2 : ℝ) ^ n; positivity)
    simpa only [Real.log_pow] using h
  have hn : (3 : ℕ) ^ b = (2 : ℕ) ^ n := by exact_mod_cast he
  have hd : 3 ∣ (2 : ℕ) ^ n := hn ▸ dvd_pow_self 3 (Nat.ne_of_gt hb)
  have : 3 ∣ (2 : ℕ) := Nat.Prime.dvd_of_dvd_pow (by decide) hd
  norm_num at this

theorem alpha_irrational : Irrational alpha := by
  rintro ⟨q, hq⟩
  have hqpos : 0 < q := by exact_mod_cast (hq.symm ▸ alpha_pos)
  have hn : 0 ≤ q.num := (Rat.num_nonneg.mpr hqpos.le)
  have he : (q.den : ℝ) * Real.log 3 = (q.num.toNat : ℝ) * Real.log 2 := by
    have hcast : (q : ℝ) = (q.num.toNat : ℝ) / (q.den : ℝ) := by
      conv_lhs => rw [← Rat.num_div_den q]
      push_cast
      have hncast : (q.num.toNat : ℝ) = (q.num : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hn
      rw [hncast]
    rw [hcast] at hq
    have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
    dsimp [alpha] at hq
    have hc := (div_eq_div_iff hd (ne_of_gt log_two_pos)).mp hq
    nlinarith [hc]
  exact mul_log_three_ne_mul_log_two q.pos q.num.toNat he

theorem mul_alpha_irrational {b : ℕ} (hb : 0 < b) : Irrational ((b : ℝ) * alpha) :=
  alpha_irrational.natCast_mul (Nat.ne_of_gt hb)

theorem mul_alpha_ne_int {b : ℕ} (hb : 0 < b) (z : ℤ) :
    (b : ℝ) * alpha ≠ (z : ℝ) := (mul_alpha_irrational hb).ne_int z

theorem a_cast_eq_ceil (b : ℕ) : (a b : ℝ) = (⌈(b : ℝ) * alpha⌉ : ℤ) :=
  natCast_ceil_eq_intCast_ceil (mul_nonneg (Nat.cast_nonneg b) alpha_pos.le)

theorem ceil_gap {b : ℕ} (hb : 0 < b) :
    0 < (a b : ℝ) - (b : ℝ) * alpha ∧ (a b : ℝ) - (b : ℝ) * alpha < 1 := by
  have hle : (b : ℝ) * alpha ≤ (a b : ℝ) := Nat.le_ceil _
  have hne : (b : ℝ) * alpha ≠ (a b : ℝ) := (mul_alpha_irrational hb).ne_nat _
  have hlt := Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg b) alpha_pos.le)
  exact ⟨sub_pos.mpr (lt_of_le_of_ne hle hne), by dsimp [a]; linarith⟩

theorem a_pos {b : ℕ} (hb : 0 < b) : 0 < a b := by
  have h := (ceil_gap hb).1
  have : (0 : ℝ) < a b := lt_of_le_of_lt
    (mul_nonneg (Nat.cast_nonneg b) alpha_pos.le) (sub_pos.mp h)
  exact_mod_cast this

@[simp] theorem R_cast (b : ℕ) : (R b : ℝ) = (2 : ℝ) ^ a b / (3 : ℝ) ^ b := by
  simp [R]

theorem R_pos (b : ℕ) : (0 : ℚ) < R b := by unfold R; positivity

theorem log_R (b : ℕ) :
    Real.log (R b : ℝ) = ((a b : ℝ) - (b : ℝ) * alpha) * Real.log 2 := by
  rw [R_cast, Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  dsimp [alpha]
  field_simp

theorem R_mem_Ioo {b : ℕ} (hb : 0 < b) : (1 : ℝ) < R b ∧ (R b : ℝ) < 2 := by
  have hp : (0 : ℝ) < R b := by exact_mod_cast R_pos b
  have hg := ceil_gap hb
  constructor
  · apply (Real.log_pos_iff hp.le).mp
    rw [log_R]
    exact mul_pos hg.1 log_two_pos
  · apply (Real.strictMonoOn_log.lt_iff_lt hp (by norm_num)).mp
    rw [log_R]
    nlinarith [mul_lt_mul_of_pos_right hg.2 log_two_pos]

theorem R_mem_Ioo_rat {b : ℕ} (hb : 0 < b) : (1 : ℚ) < R b ∧ R b < 2 := by
  exact_mod_cast R_mem_Ioo hb

theorem R_coprime (b : ℕ) : Nat.Coprime (2 ^ a b) (3 ^ b) :=
  ((by decide : Nat.Coprime 2 3).pow_left (a b)).pow_right b

@[simp] theorem R_num (b : ℕ) : (R b).num = (2 : ℤ) ^ a b := by
  have h := Rat.num_div_eq_of_coprime (a := (2 : ℤ) ^ a b)
    (b := (3 : ℤ) ^ b) (by positivity) (by simpa using R_coprime b)
  simpa [R] using h

@[simp] theorem R_den (b : ℕ) : (R b).den = 3 ^ b := by
  have h := Rat.den_div_eq_of_coprime (a := (2 : ℤ) ^ a b)
    (b := (3 : ℤ) ^ b) (by positivity) (by simpa using R_coprime b)
  have h' : ((R b).den : ℤ) = (3 : ℤ) ^ b := by simpa [R] using h
  exact_mod_cast h'

theorem Phi_R {b : ℕ} (hb : 0 < b) : Phi (R b) = Int.fract ((b : ℝ) * alpha) := by
  have hn : Int.fract ((b : ℝ) * alpha) ≠ 0 := by
    intro h
    have he : (b : ℝ) * alpha = (⌊(b : ℝ) * alpha⌋ : ℤ) := by
      simpa only [Int.fract, sub_eq_zero] using h
    exact mul_alpha_ne_int hb _ he
  have hc := Int.ceil_sub_self_eq hn
  rw [← a_cast_eq_ceil] at hc
  unfold Phi
  rw [log_R, mul_div_cancel_right₀ _ (ne_of_gt log_two_pos)]
  linarith

/-- Separation of distinct canonical reduced fractions, in the real metric. -/
theorem rational_separation {r s : ℚ} (hne : r ≠ s) :
    1 / ((r.den : ℝ) * (s.den : ℝ)) ≤ |(r : ℝ) - (s : ℝ)| := by
  have hr : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hs : (0 : ℝ) < s.den := by exact_mod_cast s.pos
  have hn : r.num * (s.den : ℤ) - s.num * (r.den : ℤ) ≠ 0 := by
    intro h
    apply hne
    apply Rat.eq_iff_mul_eq_mul.mpr
    linarith
  have hi := Int.one_le_abs hn
  have hi' : (1 : ℝ) ≤ |(r.num : ℝ) * s.den - (s.num : ℝ) * r.den| := by
    exact_mod_cast hi
  have he : (r : ℝ) - (s : ℝ) =
      ((r.num : ℝ) * s.den - (s.num : ℝ) * r.den) / (r.den * s.den) := by
    conv_lhs => rw [← Rat.num_div_den r, ← Rat.num_div_den s]
    push_cast
    field_simp
  rw [he, abs_div, abs_of_pos (mul_pos hr hs)]
  exact div_le_div_of_nonneg_right hi' (mul_pos hr hs).le

theorem R_separation (b : ℕ) {s : ℚ} (hne : R b ≠ s) :
    1 / ((3 : ℝ) ^ b * (s.den : ℝ)) ≤ |(R b : ℝ) - (s : ℝ)| := by
  simpa using rational_separation hne

theorem R_injective : Function.Injective R := by
  intro b c h
  have hd := congrArg Rat.den h
  simp only [R_den] at hd
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) hd

/-- Uniqueness of the power-of-two numerator for a fixed denominator. -/
theorem exponent_unique {b n : ℕ}
    (h : (1 : ℝ) < (2 : ℝ) ^ n / (3 : ℝ) ^ b ∧
      (2 : ℝ) ^ n / (3 : ℝ) ^ b < 2) : n = a b := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ n / (3 : ℝ) ^ b := by positivity
  have hl : Real.log ((2 : ℝ) ^ n / (3 : ℝ) ^ b) =
      (n : ℝ) * Real.log 2 - (b : ℝ) * Real.log 3 := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  have hlo := Real.log_pos h.1
  have hhi := Real.log_lt_log hp h.2
  rw [hl] at hlo hhi
  have ha : alpha * Real.log 2 = Real.log 3 :=
    div_mul_cancel₀ _ (ne_of_gt log_two_pos)
  have hlow : (b : ℝ) * alpha < n := by
    apply (mul_lt_mul_iff_left₀ log_two_pos).mp
    nlinarith [ha]
  have hupp : (n : ℝ) < (b : ℝ) * alpha + 1 := by
    apply (mul_lt_mul_iff_left₀ log_two_pos).mp
    nlinarith [ha]
  have hnpos : 0 < n := by
    have : (0 : ℝ) < n := lt_of_le_of_lt
      (mul_nonneg (Nat.cast_nonneg b) alpha_pos.le) hlow
    exact_mod_cast this
  symm
  apply (Nat.ceil_eq_iff (Nat.ne_of_gt hnpos)).mpr
  constructor
  · rw [Nat.cast_sub hnpos, Nat.cast_one]
    linarith
  · exact hlow.le

/-- A canonical rational in (1,2) with the specified numerator and denominator
is precisely the manuscript's fraction. -/
theorem R_unique {b : ℕ} {s : ℚ}
    (hs : (1 : ℚ) < s ∧ s < 2) (hd : s.den = 3 ^ b)
    (hn : ∃ n : ℕ, s.num = (2 : ℤ) ^ n) : s = R b := by
  obtain ⟨n, hn⟩ := hn
  have he : s = (2 : ℚ) ^ n / (3 : ℚ) ^ b := by
    conv_lhs => rw [← Rat.num_div_den s]
    rw [hn, hd]
    push_cast
    rfl
  have hr : (1 : ℝ) < (2 : ℝ) ^ n / (3 : ℝ) ^ b ∧
      (2 : ℝ) ^ n / (3 : ℝ) ^ b < 2 := by
    have hs' : (1 : ℝ) < (s : ℝ) ∧ (s : ℝ) < 2 := by exact_mod_cast hs
    simpa only [he, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using hs'
  rw [he, exponent_unique hr]
  rfl

/-- The elementary height restriction preceding Lemma 3.2. -/
theorem exceptional_den_bound {b : ℕ} {ν : ℝ} {s : ℚ} (h : Exceptional b ν s) :
    16 * (s.den : ℝ) ^ (ν - 1) < (3 : ℝ) ^ b := by
  obtain ⟨_, _, _, _, _, hne, herr⟩ := h
  have hd : (0 : ℝ) < s.den := by exact_mod_cast s.pos
  have hp : (0 : ℝ) < (s.den : ℝ) ^ ν := Real.rpow_pos_of_pos hd _
  have hs := lt_of_le_of_lt (R_separation b hne.symm) herr
  have hcross : 16 * (s.den : ℝ) ^ ν < (3 : ℝ) ^ b * s.den :=
    (one_div_lt_one_div (by positivity) (by positivity)).mp hs
  rw [Real.rpow_sub_one (ne_of_gt hd), ← mul_div_assoc]
  exact (div_lt_iff₀ hd).mpr hcross

/-- Raising the denominator cutoff can only remove exceptional indices. -/
theorem exceptionalCount_antitone (N : ℕ) (ν : ℝ) :
    Antitone (fun D : ℝ => exceptionalCount N D ν) := by
  classical
  intro D E hDE
  apply Finset.card_le_card
  intro b hb
  simp only [Finset.mem_filter] at hb ⊢
  obtain ⟨hb, s, hs, hE⟩ := hb
  exact ⟨hb, s, hs, hDE.trans_lt hE⟩

end ErdosMahlerAudit
