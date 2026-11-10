module

public import ErdosMahlerAudit.Gate08.Selection
public import Mathlib.Algebra.Order.Archimedean.Basic

/-! Least natural exponent above a real square, TeX 816–817, 914. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate08

theorem exists_power_above (x : ℝ) : ∃ k : ℕ, x ^ 2 ≤ (2 : ℝ) ^ k := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (x ^ 2) (by norm_num : (1 : ℝ) < 2)
  exact ⟨k, hk.le⟩

noncomputable def leastExponent (x : ℝ) : ℕ := by
  classical
  exact Nat.find (exists_power_above x)

noncomputable def leastPower (x : ℝ) : ℕ := 2 ^ leastExponent x

theorem leastExponent_spec (x : ℝ) : x ^ 2 ≤ (2 : ℝ) ^ leastExponent x := by
  classical
  exact Nat.find_spec (exists_power_above x)

theorem leastExponent_min {x : ℝ} {j : ℕ} (hj : j < leastExponent x) :
    (2 : ℝ) ^ j < x ^ 2 := by
  classical
  exact lt_of_not_ge (Nat.find_min (exists_power_above x) hj)

theorem leastExponent_pos {x : ℝ} (hx : 2 ≤ x) : 1 ≤ leastExponent x := by
  have h := leastExponent_spec x
  by_contra hn
  have he : leastExponent x = 0 := by omega
  rw [he, pow_zero] at h
  nlinarith

theorem leastPower_bounds {x : ℝ} (hx : 2 ≤ x) :
    x ^ 2 ≤ (leastPower x : ℝ) ∧ (leastPower x : ℝ) < 2 * x ^ 2 := by
  have hk := leastExponent_pos hx
  have hprev := leastExponent_min (x := x) (j := leastExponent x - 1) (by omega)
  have he : leastExponent x = (leastExponent x - 1) + 1 := by omega
  constructor
  · simpa only [leastPower, Nat.cast_pow, Nat.cast_ofNat] using leastExponent_spec x
  · simp only [leastPower, Nat.cast_pow, Nat.cast_ofNat]
    rw [he, pow_succ]
    linarith

theorem leastPower_pos (x : ℝ) : 0 < leastPower x := pow_pos (by decide) _

theorem leastPower_log {x : ℝ} (hx : 2 ≤ x) :
    Real.log (leastPower x : ℝ) < Real.log 2 + 2 * Real.log x := by
  have hx0 : 0 < x := by linarith
  have hq0 : (0 : ℝ) < leastPower x := by exact_mod_cast leastPower_pos x
  have h := Real.strictMonoOn_log hq0 (by change 0 < 2 * x ^ 2; positivity) (leastPower_bounds hx).2
  simpa only [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt (sq_pos_of_pos hx0)),
    Real.log_pow, Nat.cast_ofNat] using h

theorem leastExponent_log_bound {x : ℝ} (hx : 2 ≤ x) :
    (leastExponent x : ℝ) * Real.log 2 < Real.log 2 + 2 * Real.log x := by
  simpa only [leastPower, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using leastPower_log hx

end ErdosMahlerAudit.Gate08
