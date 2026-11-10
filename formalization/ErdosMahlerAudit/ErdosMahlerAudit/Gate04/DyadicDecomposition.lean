module

public import ErdosMahlerAudit.Gate04.ShellCounting

/-! Finite truncated dyadic covers and uniform geometric sums, TeX 513–526. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate04
open scoped BigOperators

noncomputable def dyadicScale (D : ℝ) (i : ℕ) : ℝ := (2 : ℝ) ^ i * D

@[simp] theorem dyadicScale_zero (D : ℝ) : dyadicScale D 0 = D := by
  simp [dyadicScale]

theorem dyadicScale_succ (D : ℝ) (i : ℕ) :
    dyadicScale D (i + 1) = 2 * dyadicScale D i := by
  simp only [dyadicScale, pow_succ]
  ring

theorem dyadicScale_pos {D : ℝ} (hD : 0 < D) (i : ℕ) : 0 < dyadicScale D i :=
  mul_pos (by positivity) hD

theorem le_dyadicScale {D : ℝ} (hD : 0 ≤ D) (i : ℕ) : D ≤ dyadicScale D i := by
  have hp : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
  simpa [dyadicScale] using mul_le_mul_of_nonneg_right hp hD

/-- The first scale reaching U. All indices before it are active, and the
upper endpoint U is included. This also allows U ≤ D, in which case k=0. -/
theorem exists_dyadic_cutoff {D U : ℝ} (hD : 0 < D) :
    ∃ k : ℕ, U ≤ dyadicScale D k ∧ ∀ i : ℕ, i < k → dyadicScale D i < U := by
  have hex : ∃ k : ℕ, U ≤ dyadicScale D k := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (U / D) (by norm_num : (1 : ℝ) < 2)
    exact ⟨k, ((div_lt_iff₀ hD).mp hk).le⟩
  classical
  exact ⟨Nat.find hex, Nat.find_spec hex,
    fun i hi => lt_of_not_ge (Nat.find_min hex hi)⟩

/-- Exact truncated coverage for an arbitrary real v, including v=U and
v at a dyadic upper boundary. No integral-cutoff assumption is used. -/
theorem dyadic_cover {D U v : ℝ} {k : ℕ} (hDv : D < v)
    (hvU : v ≤ U) (hUk : U ≤ dyadicScale D k) :
    ∃ i ∈ Finset.range k, dyadicScale D i < v ∧
      v ≤ min (2 * dyadicScale D i) U := by
  have hcover : ∀ k : ℕ, v ≤ dyadicScale D k →
      ∃ i ∈ Finset.range k, dyadicScale D i < v ∧ v ≤ 2 * dyadicScale D i := by
    intro k
    induction k with
    | zero => simpa using (not_le_of_gt hDv)
    | succ k ih =>
      intro hk
      by_cases hv : v ≤ dyadicScale D k
      · obtain ⟨i, hi, hlo, hhi⟩ := ih hv
        exact ⟨i, Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hi)), hlo, hhi⟩
      · exact ⟨k, Finset.mem_range.mpr (Nat.lt_succ_self k), lt_of_not_ge hv,
          by simpa only [dyadicScale_succ] using hk⟩
  obtain ⟨i, hi, hlo, hhi⟩ := hcover k (hvU.trans hUk)
  exact ⟨i, hi, hlo, le_min hhi hvU⟩

theorem dyadic_ratio_le_quarter {ν : ℝ} (hν : 4 ≤ ν) :
    (2 : ℝ) ^ (2 - ν) ≤ 1 / 4 := by
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (by linarith : 2 - ν ≤ -(2 : ℝ))
  norm_num [Real.rpow_neg] at h ⊢
  exact h

/-- Uniform finite geometric estimate, including the limiting ratio 1/4. -/
theorem geometric_sum_le_four_thirds {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 4)
    (k : ℕ) : (∑ i ∈ Finset.range k, q ^ i) ≤ 4 / 3 := by
  have hid : (∑ i ∈ Finset.range k, q ^ i) * (1 - q) = 1 - q ^ k := by
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, pow_succ]; nlinarith [ih]
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range k, q ^ i :=
    Finset.sum_nonneg (fun i _ => pow_nonneg hq0 i)
  nlinarith [pow_nonneg hq0 k, mul_nonneg hsum0 (by linarith : 0 ≤ 1 / 4 - q)]

theorem dyadicScale_rpow {D : ℝ} (hD : 0 ≤ D) (p : ℝ) (i : ℕ) :
    (dyadicScale D i) ^ p = ((2 : ℝ) ^ p) ^ i * D ^ p := by
  rw [dyadicScale, Real.mul_rpow (by positivity) hD,
    ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm (i : ℝ) p,
    Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]

theorem dyadic_negative_sum {D ν : ℝ} (hD : 0 < D) (hν : 4 ≤ ν) (k : ℕ) :
    (∑ i ∈ Finset.range k, (dyadicScale D i) ^ (2 - ν)) ≤ (4 / 3) * D ^ (2 - ν) := by
  simp_rw [dyadicScale_rpow hD.le]
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right
    (geometric_sum_le_four_thirds (Real.rpow_nonneg (by norm_num) _)
      (dyadic_ratio_le_quarter hν) k) (Real.rpow_nonneg hD.le _)

/-- Telescoping identity makes the positive-power sum finite and explicit. -/
theorem dyadic_square_sum_identity (D : ℝ) (k : ℕ) :
    3 * (∑ i ∈ Finset.range k, (dyadicScale D i) ^ 2) =
      (dyadicScale D k) ^ 2 - D ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, dyadicScale_succ]; nlinarith [ih]

theorem dyadic_square_sum {D U : ℝ} (hD : 0 < D) (k : ℕ)
    (hactive : ∀ i : ℕ, i < k → dyadicScale D i < U) :
    (∑ i ∈ Finset.range k, (dyadicScale D i) ^ 2) ≤ (4 / 3) * U ^ 2 := by
  cases k with
  | zero => simp only [Finset.range_zero, Finset.sum_empty]; positivity
  | succ k =>
    have hl := hactive k (Nat.lt_succ_self k)
    have hp := dyadicScale_pos hD k
    have hid := dyadic_square_sum_identity D (k + 1)
    rw [dyadicScale_succ] at hid
    nlinarith [sq_nonneg D, mul_nonneg (by linarith : 0 ≤ U - dyadicScale D k)
      (by linarith : 0 ≤ U + dyadicScale D k)]

end ErdosMahlerAudit.Gate04
