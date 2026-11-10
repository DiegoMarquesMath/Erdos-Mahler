module

public import ErdosMahlerAudit.Gate05.LocalProduct
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Rational separation and real-power estimates in TeX 598–613. -/

public section
namespace ErdosMahlerAudit.Gate05

theorem violation_den_lt {b : ℕ} {s : ℚ} {ε : ℝ}
    (hε : 0 < ε) (hne : s ≠ R b)
    (herr : |(R b : ℝ) - s| < (S b : ℝ) ^ (-ε) * (v s : ℝ) ^ (-2 : ℝ)) :
    (v s : ℝ) < (S b : ℝ) ^ (1 - ε) ∧ (v s : ℝ) < S b := by
  have hS : (0 : ℝ) < S b := by exact_mod_cast S_pos b
  have hv : (0 : ℝ) < v s := by exact_mod_cast v_pos s
  have hS1 : (1 : ℝ) ≤ S b := by exact_mod_cast S_pos b
  have hsep : 1 / ((S b : ℝ) * v s) ≤ |(R b : ℝ) - s| := by
    simpa only [S, v, Nat.cast_pow, Nat.cast_ofNat] using R_separation b hne.symm
  have hh := hsep.trans_lt herr
  rw [Real.rpow_neg hv.le, Real.rpow_two, ← div_eq_mul_inv] at hh
  have hc := (div_lt_div_iff₀ (mul_pos hS hv) (sq_pos_of_pos hv)).mp hh
  have hl : (v s : ℝ) < (S b : ℝ) * (S b : ℝ) ^ (-ε) := by nlinarith
  have he : (S b : ℝ) ^ (1 - ε) = (S b : ℝ) * (S b : ℝ) ^ (-ε) := by
    rw [sub_eq_add_neg, Real.rpow_add hS, Real.rpow_one]
  have hp : (S b : ℝ) ^ (-ε) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hS1 (neg_nonpos.mpr hε.le)
  exact ⟨by rwa [he], hl.trans_le (by nlinarith)⟩

theorem violation_height_lt {b : ℕ} {s : ℚ} {ε : ℝ}
    (hb : 0 < b) (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (hε : 0 < ε) (hne : s ≠ R b)
    (herr : |(R b : ℝ) - s| < (S b : ℝ) ^ (-ε) * (v s : ℝ) ^ (-2 : ℝ)) :
    (H b s : ℝ) < 2 * (S b : ℝ) ^ 2 := by
  have hv := (violation_den_lt hε hne herr).2
  have hH : (H b s : ℝ) ≤ 2 * S b * v s := by exact_mod_cast H_le_two_S_v hb hs1 hs2
  have hS : (0 : ℝ) < S b := by exact_mod_cast S_pos b
  nlinarith

theorem violation_product_lt {b : ℕ} {s : ℚ} {ε : ℝ}
    (hb : 0 < b) (hs1 : 1 ≤ s) (hs2 : s ≤ 2)
    (herr : |(R b : ℝ) - s| < (S b : ℝ) ^ (-ε) * (v s : ℝ) ^ (-2 : ℝ)) :
    localProduct (U b s) (W b s) < 2 * (S b : ℝ) ^ (-ε) := by
  have hv : (0 : ℝ) < v s := by exact_mod_cast v_pos s
  have h := (localProduct_le_error hb hs1 hs2).trans_lt
    (mul_lt_mul_of_pos_left herr (by positivity : 0 < 2 * (v s : ℝ) ^ 2))
  have he : 2 * (v s : ℝ) ^ 2 * ((S b : ℝ) ^ (-ε) * (v s : ℝ) ^ (-2 : ℝ)) =
      2 * (S b : ℝ) ^ (-ε) := by
    rw [Real.rpow_neg hv.le, Real.rpow_two]
    field_simp
  rwa [he] at h

theorem scale_power_bound {T Q ε : ℝ} (hT : 0 < T) (hQ : 0 < Q) (hε : 0 < ε)
    (hbound : T ≤ 2 * Q ^ 2) :
    2 * Q ^ (-ε) ≤ (2 : ℝ) ^ (1 + ε / 2) * T ^ (-ε / 2) := by
  have h := Real.rpow_le_rpow_of_nonpos hT hbound (by linarith : -ε / 2 ≤ 0)
  have he : (2 : ℝ) ^ (1 + ε / 2) * (2 * Q ^ 2) ^ (-ε / 2) = 2 * Q ^ (-ε) := by
    rw [Real.mul_rpow (by norm_num) (sq_nonneg Q), ← mul_assoc,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have hx : (1 + ε / 2) + -ε / 2 = 1 := by ring
    rw [hx, Real.rpow_one, ← Real.rpow_natCast, ← Real.rpow_mul hQ.le]
    simp only [Nat.cast_ofNat, show (2 : ℝ) * (-ε / 2) = -ε by ring]
  rw [← he]
  exact mul_le_mul_of_nonneg_left h (Real.rpow_nonneg (by norm_num) _)

theorem delta_bounds {ε : ℝ} (hε : 0 < ε) :
    0 < min (ε / 4) (1 / 2 : ℝ) ∧ min (ε / 4) (1 / 2 : ℝ) < 1 ∧
      0 < ε / 2 - min (ε / 4) (1 / 2 : ℝ) := by
  have h1 := min_le_left (ε / 4) (1 / 2 : ℝ)
  have h2 := min_le_right (ε / 4) (1 / 2 : ℝ)
  exact ⟨lt_min (by linarith) (by norm_num), by linarith, by linarith⟩

theorem euclidean_power_bound {x y T δ : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hxT : x ≤ T) (hyT : y ≤ T) (hδ : 0 < δ) :
    (2 : ℝ) ^ (-δ / 2) * T ^ (-δ) ≤ (x ^ 2 + y ^ 2) ^ (-δ / 2) := by
  have hT : 0 < T := hx.trans_le hxT
  have hnorm : x ^ 2 + y ^ 2 ≤ 2 * T ^ 2 := by nlinarith [sq_nonneg (T-x), sq_nonneg (T-y)]
  have h := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < x ^ 2 + y ^ 2)
    hnorm (by linarith : -δ / 2 ≤ 0)
  have he : (2 * T ^ 2) ^ (-δ / 2) = (2 : ℝ) ^ (-δ / 2) * T ^ (-δ) := by
    rw [Real.mul_rpow (by norm_num) (sq_nonneg T), ← Real.rpow_natCast,
      ← Real.rpow_mul hT.le]
    simp only [Nat.cast_ofNat, show (2 : ℝ) * (-δ / 2) = -δ by ring]
  rwa [he] at h

/-- The threshold depends on ε, never on the particular pair. -/
theorem exists_euclidean_threshold {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ x y : ℝ, 0 < x → 0 < y → M ≤ max x y →
      (2 : ℝ) ^ (1 + ε / 2) * (max x y) ^ (-ε / 2) <
        (x ^ 2 + y ^ 2) ^ (-min (ε / 4) (1 / 2 : ℝ) / 2) := by
  let δ := min (ε / 4) (1 / 2 : ℝ)
  let C := (2 : ℝ) ^ (1 + ε / 2)
  have hd := delta_bounds hε
  obtain ⟨M, hM⟩ := Filter.tendsto_atTop_atTop.mp
    (tendsto_rpow_atTop hd.2.2) (C * (2 : ℝ) ^ (δ / 2) + 1)
  refine ⟨max 1 M, le_max_left _ _, ?_⟩
  intro x y hx hy hlarge
  let T := max x y
  have hT : 0 < T := hx.trans_le (le_max_left _ _)
  have hpow : C * (2 : ℝ) ^ (δ / 2) < T ^ (ε / 2 - δ) := by
    have := hM T ((le_max_right _ _).trans hlarge)
    linarith
  rw [Real.rpow_sub hT] at hpow
  have hcross := (lt_div_iff₀ (Real.rpow_pos_of_pos hT δ)).mp hpow
  have hstrict : C * T ^ (-ε / 2) < (2 : ℝ) ^ (-δ / 2) * T ^ (-δ) := by
    have hTe := (Real.rpow_pos_of_pos hT (ε / 2)).ne'
    have hTd := (Real.rpow_pos_of_pos hT δ).ne'
    have h2d := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (δ / 2)).ne'
    rw [show -ε / 2 = -(ε / 2) by ring, show -δ / 2 = -(δ / 2) by ring,
      Real.rpow_neg hT.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg hT.le]
    apply (mul_lt_mul_iff_right₀ (by positivity : 0 < T ^ (ε / 2) *
      ((2 : ℝ) ^ (δ / 2) * T ^ δ))).mp
    field_simp
    nlinarith [hcross]
  exact hstrict.trans_le (euclidean_power_bound hx hy.le (le_max_left _ _) (le_max_right _ _) hd.1)

end ErdosMahlerAudit.Gate05
