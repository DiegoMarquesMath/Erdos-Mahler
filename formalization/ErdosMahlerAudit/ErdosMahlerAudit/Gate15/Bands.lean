module

public import ErdosMahlerAudit.Gate15.Partition

/-! Sharp finite-band estimates, using the original admissible child. TeX 387–442. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate15
open Gate14

theorem cutoff_error {B v τ : ℝ} (hB : 0 < B) (hv : 0 < v)
    (hcut : 6 * v ≤ B ^ (τ - 1)) :
    3 * B ^ (-τ) ≤ 1 / (2 * v * B) := by
  rw [Real.rpow_sub_one hB.ne'] at hcut
  have hc := (le_div_iff₀ hB).mp hcut
  rw [Real.rpow_neg hB.le, ← one_div, mul_one_div]
  apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hB _) (by positivity)).mpr
  nlinarith

theorem next_cutoff {S v τ : ℝ} (hS : 3 ≤ S) (hv : v < S) (hτ : 4 ≤ τ) :
    6 * v < S ^ 3 ∧ S ^ 3 ≤ S ^ (τ - 1) := by
  have hs : 6 < S ^ 2 := by nlinarith
  constructor
  · nlinarith [mul_pos (by linarith : 0 < S) (sub_pos.mpr hs)]
  · simpa only [Real.rpow_ofNat] using
      Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ S)
        (by linarith : (3 : ℝ) ≤ τ - 1)

theorem cutoff_error_strict {B v τ : ℝ} (hB : 0 < B) (hv : 0 < v)
    (hcut : 6 * v < B ^ (τ - 1)) :
    3 * B ^ (-τ) < 1 / (2 * v * B) := by
  rw [Real.rpow_sub_one hB.ne'] at hcut
  have hc := (lt_div_iff₀ hB).mp hcut
  rw [Real.rpow_neg hB.le, ← one_div, mul_one_div]
  apply (div_lt_div_iff₀ (Real.rpow_pos_of_pos hB _) (by positivity)).mpr
  nlinarith

theorem quadratic_to_band {v ν : ℝ} (hv : 1 ≤ v) (hν : 4 < ν) :
    1 / (32 * v ^ ν) ≤ 1 / (2 * v ^ 2) := by
  have hp : 0 < v := by linarith
  have he : v ^ 2 ≤ v ^ ν := by
    simpa only [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_le hv (by linarith : (2 : ℝ) ≤ ν)
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [Real.rpow_pos_of_pos hp ν]

variable {τ : ℝ} {t0 : ℕ} {f : List Bool → ℕ} {ξ : (ℕ → Bool) → ℝ} {K : Set ℝ}

theorem actual_successor_admissible (hC : Gate13.CantorSpec τ t0 f ξ K)
    (ε : ℕ → Bool) (j : ℕ) :
    ∃ N : ℕ, N ∈ convergentDenominators ∧ 3 ^ t f ε j < N ∧
      t f ε (j + 1) ∈ Gate02.admissibleIndices (t f ε j) τ N := by
  obtain ⟨N, hN, hNt, hl, hr⟩ := (hC.tree.pairs (Gate13.«prefix» ε j)).admissible
  refine ⟨N, hN, hNt, ?_⟩
  dsimp only [t]
  rw [Gate13.prefix_succ]
  cases h : ε j with
  | false => exact hl
  | true => exact hr

theorem cutoff_identity (ε : ℕ → Bool) (j : ℕ) :
    Gate02.cutoff (t f ε j) τ = (Q f ε j : ℝ) ^ (τ - 1) / 6 := by
  simp only [Gate02.cutoff, Q, Nat.cast_pow, Nat.cast_ofNat]

theorem small_case (hA : ArithmeticLowerSpec τ t0 f ξ)
    (ε : ℕ → Bool) (j : ℕ) (q : ℚ) (hne : q ≠ r f ε j)
    (hQv : Q f ε j ≤ q.den)
    (hcut : (q.den : ℝ) ≤ Gate02.cutoff (t f ε j) τ) :
    1 / (2 * (q.den : ℝ) ^ 2) ≤ |ξ ε - (q : ℝ)| := by
  have hv : (0 : ℝ) < q.den := by exact_mod_cast q.pos
  have hQ : (0 : ℝ) < Q f ε j := by exact_mod_cast hA.denominator_pos ε j
  have hQv' : (Q f ε j : ℝ) ≤ q.den := by exact_mod_cast hQv
  rw [cutoff_identity] at hcut
  have hc : 6 * (q.den : ℝ) ≤ (Q f ε j : ℝ) ^ (τ - 1) := by linarith
  have herr := (hA.legendre ε j).2.1.le.trans (cutoff_error hQ hv hc)
  have hsep := rational_separation hne.symm
  rw [hA.denominator] at hsep
  have htri := abs_sub_le (r f ε j : ℝ) (ξ ε) (q : ℝ)
  rw [abs_sub_comm (r f ε j : ℝ) (ξ ε)] at htri
  have he : 1 / ((Q f ε j : ℝ) * q.den) = 2 * (1 / (2 * (q.den : ℝ) * Q f ε j)) := by
    field_simp
  have hhalf : 1 / (2 * (q.den : ℝ) * Q f ε j) ≤ |ξ ε - (q : ℝ)| := by
    rw [he] at hsep
    linarith
  apply le_trans _ hhalf
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

theorem not_next (hA : ArithmeticLowerSpec τ t0 f ξ)
    (ε : ℕ → Bool) (j : ℕ) (q : ℚ) (hv : q.den < Q f ε (j + 1)) :
    q ≠ r f ε (j + 1) := by
  intro he
  rw [he, hA.denominator] at hv
  exact (lt_irrefl _) hv

theorem next_error (hA : ArithmeticLowerSpec τ t0 f ξ) (hτ : 4 ≤ τ)
    (ε : ℕ → Bool) (j : ℕ) (q : ℚ) (hv : q.den < Q f ε (j + 1)) :
    |ξ ε - (r f ε (j + 1) : ℝ)| <
      1 / (2 * (q.den : ℝ) * Q f ε (j + 1)) := by
  have hS : (0 : ℝ) < Q f ε (j + 1) := by exact_mod_cast hA.denominator_pos ε _
  have hvpos : (0 : ℝ) < q.den := by exact_mod_cast q.pos
  have hc := next_cutoff (S := (Q f ε (j + 1) : ℝ)) (v := (q.den : ℝ))
    (by exact_mod_cast hA.denominator_three ε (j + 1))
    (by exact_mod_cast hv) hτ
  exact (hA.legendre ε (j + 1)).2.1.trans (cutoff_error_strict hS hvpos (hc.1.trans_le hc.2))

theorem large_case (hC : Gate13.CantorSpec τ t0 f ξ K)
    (hA : ArithmeticLowerSpec τ t0 f ξ) (hτ : 4 ≤ τ)
    (ε : ℕ → Bool) (j : ℕ) (q : ℚ) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (hv : q.den < Q f ε (j + 1))
    (hcut : Gate02.cutoff (t f ε j) τ < (q.den : ℝ)) :
    1 / (32 * (q.den : ℝ) ^ Gate02.nu (t f ε j)) ≤ |ξ ε - (q : ℝ)| := by
  have hne := not_next hA ε j q hv
  obtain ⟨N, _, hN, hb⟩ := actual_successor_admissible hC ε j
  have hNpos : 0 < N := (by positivity : 0 < 3 ^ t f ε j).trans hN
  have ha := Gate02.admissible_approximation_lower (hA.index_pos ε j) hNpos hb
    q hq1 hq2 hne hcut
  change 1 / (16 * (q.den : ℝ) ^ Gate02.nu (t f ε j)) ≤
    |(r f ε (j + 1) : ℝ) - (q : ℝ)| at ha
  have hsep := rational_separation hne.symm
  rw [hA.denominator] at hsep
  have he := next_error hA hτ ε j q hv
  have htri := abs_sub_le (r f ε (j + 1) : ℝ) (ξ ε) (q : ℝ)
  rw [abs_sub_comm (r f ε (j + 1) : ℝ) (ξ ε)] at htri
  have hid : 1 / ((Q f ε (j + 1) : ℝ) * q.den) =
      2 * (1 / (2 * (q.den : ℝ) * Q f ε (j + 1))) := by field_simp
  have hid' : 1 / (16 * (q.den : ℝ) ^ Gate02.nu (t f ε j)) =
      2 * (1 / (32 * (q.den : ℝ) ^ Gate02.nu (t f ε j))) := by field_simp; ring
  rw [hid] at hsep
  rw [hid'] at ha
  linarith

theorem nonprescribed_band (hC : Gate13.CantorSpec τ t0 f ξ K)
    (hA : ArithmeticLowerSpec τ t0 f ξ) (hτ : 4 ≤ τ)
    (ε : ℕ → Bool) (j : ℕ) (q : ℚ) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (hband : Q f ε j ≤ q.den ∧ q.den < Q f ε (j + 1)) (hne : q ≠ r f ε j) :
    1 / (32 * (q.den : ℝ) ^ Gate02.nu (t f ε j)) ≤ |ξ ε - (q : ℝ)| := by
  by_cases hc : (q.den : ℝ) ≤ Gate02.cutoff (t f ε j) τ
  · exact (quadratic_to_band (by exact_mod_cast q.pos)
      (Gate02.parent_parameters (hA.index_pos ε j) τ).2.1).trans
      (small_case hA ε j q hne hband.1 hc)
  · exact large_case hC hA hτ ε j q hq1 hq2 hband.2 (lt_of_not_ge hc)

/-- Exhaustive three-way band statement, with cutoff equality in the small case. -/
theorem finite_band (hC : Gate13.CantorSpec τ t0 f ξ K)
    (hA : ArithmeticLowerSpec τ t0 f ξ) (hτ : 4 ≤ τ)
    (ε : ℕ → Bool) (j : ℕ) (q : ℚ) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (hband : Q f ε j ≤ q.den ∧ q.den < Q f ε (j + 1)) :
    (q = r f ε j ∧ q.den = Q f ε j ∧ (q.den : ℝ) ^ (-τ) < |ξ ε - (q : ℝ)|) ∨
    (q ≠ r f ε j ∧ (q.den : ℝ) ≤ Gate02.cutoff (t f ε j) τ ∧
      1 / (2 * (q.den : ℝ) ^ 2) ≤ |ξ ε - (q : ℝ)|) ∨
    (q ≠ r f ε j ∧ Gate02.cutoff (t f ε j) τ < (q.den : ℝ) ∧
      1 / (32 * (q.den : ℝ) ^ Gate02.nu (t f ε j)) ≤ |ξ ε - (q : ℝ)|) := by
  by_cases hq : q = r f ε j
  · exact Or.inl ⟨hq, prescribed_case hA ε j hq⟩
  · by_cases hc : (q.den : ℝ) ≤ Gate02.cutoff (t f ε j) τ
    · exact Or.inr (Or.inl ⟨hq, hc, small_case hA ε j q hq hband.1 hc⟩)
    · exact Or.inr (Or.inr ⟨hq, lt_of_not_ge hc,
        large_case hC hA hτ ε j q hq1 hq2 hband.2 (lt_of_not_ge hc)⟩)

end ErdosMahlerAudit.Gate15
