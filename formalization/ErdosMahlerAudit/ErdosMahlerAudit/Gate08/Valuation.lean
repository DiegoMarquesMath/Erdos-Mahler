module

public import ErdosMahlerAudit.Gate08.Height
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-! Exact rational 3-adic valuation and its height bound, TeX 936–943. -/

public section
namespace ErdosMahlerAudit.Gate08

theorem valuation_R (b : ℕ) : padicValRat 3 (R b) = -(b : ℤ) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have ht : padicValRat 3 (2 : ℚ) = 0 := by
    change padicValRat 3 ((2 : ℕ) : ℚ) = 0
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (by decide : ¬3 ∣ 2)]
    rfl
  have hh : padicValRat 3 (3 : ℚ) = 1 := padicValRat.self (by decide)
  rw [R, padicValRat.div (by positivity) (by positivity),
    padicValRat.pow, padicValRat.pow, ht, hh]
  ring

theorem valuation_R_ratio (b c : ℕ) :
    padicValRat 3 (R c / R b) = (b : ℤ) - (c : ℤ) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [padicValRat.div (R_pos c).ne' (R_pos b).ne', valuation_R, valuation_R]
  ring

theorem valuation_nat_log_bound {n : ℕ} (hn : 0 < n) :
    (padicValNat 3 n : ℝ) * Real.log 3 ≤ Real.log (n : ℝ) := by
  have hpow : (3 : ℕ) ^ padicValNat 3 n ≤ n := Nat.le_of_dvd hn pow_padicValNat_dvd
  have hpowR : (3 : ℝ) ^ padicValNat 3 n ≤ (n : ℝ) := by exact_mod_cast hpow
  simpa only [Real.log_pow] using Real.log_le_log (by positivity) hpowR

theorem valuation_height_bound {z : ℚ} (hz : 0 < z) :
    |(padicValRat 3 z : ℝ)| * Real.log 3 ≤ rationalHeight z := by
  have hn0 : 0 < z.num.natAbs := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hz.ne')
  have hn := valuation_nat_log_bound hn0
  have hd := valuation_nat_log_bound z.pos
  have hnh : Real.log (z.num.natAbs : ℝ) ≤ rationalHeight z :=
    Real.log_le_log (by exact_mod_cast hn0)
      (by exact_mod_cast le_max_left z.num.natAbs z.den)
  have hdh : Real.log (z.den : ℝ) ≤ rationalHeight z :=
    Real.log_le_log (by exact_mod_cast z.pos)
      (by exact_mod_cast le_max_right z.num.natAbs z.den)
  have hp : (padicValRat 3 z : ℝ) =
      (padicValNat 3 z.num.natAbs : ℝ) - (padicValNat 3 z.den : ℝ) := by
    simp only [padicValRat, padicValInt, Int.cast_sub, Int.cast_natCast]
  rw [hp, ← abs_of_pos log_three_pos, ← abs_mul, abs_le]
  have hnnon : (0 : ℝ) ≤ padicValNat 3 z.num.natAbs := by positivity
  have hdnon : (0 : ℝ) ≤ padicValNat 3 z.den := by positivity
  constructor <;> nlinarith [mul_nonneg hnnon log_three_pos.le,
    mul_nonneg hdnon log_three_pos.le]

/-- The elementary consequence of an exact ratio identity. This does not supply
that identity from class membership and is not the final same-class theorem. -/
theorem index_gap_of_ratio_eq {N b c : ℕ} {ν θ w : ℝ} {s t : ℚ}
    (hs : s ∈ Gate06.selectedFractions N ν θ w)
    (ht : t ∈ Gate06.selectedFractions N ν θ w)
    (he : t / s = R c / R b) :
    |(c : ℝ) - (b : ℝ)| * Real.log 3 ≤ 2 * w + Real.log 2 := by
  have h := valuation_height_bound (div_pos (Gate06.selectedFractions_positive ht)
    (Gate06.selectedFractions_positive hs))
  have hv : padicValRat 3 (t / s) = (b : ℤ) - (c : ℤ) := by
    rw [he, valuation_R_ratio]
  rw [hv, Int.cast_sub, Int.cast_natCast, Int.cast_natCast, abs_sub_comm] at h
  exact h.trans (selected_ratio_height hs ht)

end ErdosMahlerAudit.Gate08
