module

public import ErdosMahlerAudit.Gate11.Intervals

/-! Separation using the common denominator 3^c, rather than the weaker
product-denominator estimate (frozen TeX 305–317). Index order is never
identified with the order of the prescribed rational values. -/

public section
namespace ErdosMahlerAudit.Gate11

/-- The integer numerator after putting both prescribed fractions over 3^c. -/
theorem common_denominator {b c : ℕ} (hbc : b ≤ c) :
    (R b : ℝ) - (R c : ℝ) =
      (((2 : ℤ) ^ a b * 3 ^ (c - b) - 2 ^ a c : ℤ) : ℝ) / (3 : ℝ) ^ c := by
  have hp : (3 : ℝ) ^ c = (3 : ℝ) ^ b * 3 ^ (c - b) := by
    rw [← pow_add, Nat.add_sub_of_le hbc]
  push_cast
  rw [R_cast, R_cast, hp]
  field_simp

theorem common_denominator_separation {b c : ℕ} (hbc : b < c) :
    1 / (3 : ℝ) ^ c ≤ |(R b : ℝ) - (R c : ℝ)| := by
  let z : ℤ := 2 ^ a b * 3 ^ (c - b) - 2 ^ a c
  have he := common_denominator hbc.le
  have hz : z ≠ 0 := by
    intro hz
    have hv : (R b : ℝ) = (R c : ℝ) := by
      apply sub_eq_zero.mp
      rw [he]
      change (z : ℝ) / (3 : ℝ) ^ c = 0
      rw [hz]
      simp
    have hq : R b = R c := by exact_mod_cast hv
    exact (Nat.ne_of_lt hbc) (R_injective hq)
  have hi : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast Int.one_le_abs hz
  rw [he, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 3 ^ c)]
  exact div_le_div_of_nonneg_right hi (by positivity)

/-- This is the full strict chain in the manuscript, expressed with reciprocals. -/
theorem separation_chain {τ : ℝ} {b c : ℕ} (hτ : 4 ≤ τ)
    (hb : 0 < b) (hbc : b < c) (hc : c < 2 * b) :
    3 * Gate02.radius b τ < 1 / (3 : ℝ) ^ (2 * b) ∧
    1 / (3 : ℝ) ^ (2 * b) < 1 / (3 : ℝ) ^ c ∧
    1 / (3 : ℝ) ^ c ≤ |(R b : ℝ) - (R c : ℝ)| := by
  refine ⟨?_, ?_, common_denominator_separation hbc⟩
  · simpa only [mul_comm 2 b, pow_mul] using radius_extension_lt hb hτ
  · exact one_div_lt_one_div_of_lt (by positivity)
      (pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 3) hc)

/-- A strict gap between endpoints, in whichever real order actually holds. -/
theorem strictly_separated {τ : ℝ} {b c : ℕ} (hτ : 4 ≤ τ)
    (hb : 0 < b) (hbc : b < c) (hc : c < 2 * b) :
    right τ b < left τ c ∨ right τ c < left τ b := by
  obtain ⟨h1, h2, h3⟩ := separation_chain hτ hb hbc hc
  have hgap : 3 * Gate02.radius b τ < |(R b : ℝ) - (R c : ℝ)| :=
    (h1.trans h2).trans_le h3
  have hrad := (radius_strictAnti hτ hbc).le
  have hbpos := Gate02.radius_pos b τ
  have hcpos := Gate02.radius_pos c τ
  rcases le_total (R b : ℝ) (R c : ℝ) with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hgap
    left
    dsimp [right, left]
    linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hgap
    right
    dsimp [right, left]
    linarith

theorem K_disjoint {τ : ℝ} {b c : ℕ} (hτ : 4 ≤ τ)
    (hb : 0 < b) (hbc : b < c) (hc : c < 2 * b) :
    Disjoint (K τ b) (K τ c) := by
  rw [Set.disjoint_left]
  intro x hbmem hcmem
  rcases strictly_separated hτ hb hbc hc with h | h
  · exact (not_lt_of_ge (hcmem.1.trans hbmem.2)) h
  · exact (not_lt_of_ge (hbmem.1.trans hcmem.2)) h

end ErdosMahlerAudit.Gate11
