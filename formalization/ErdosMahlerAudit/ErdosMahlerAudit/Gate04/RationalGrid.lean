module

public import ErdosMahlerAudit.Gate02.Exceptional
public import Mathlib.Data.Finset.Prod

/-! Finite grids for the canonical reduced fractions in TeX lines 502–504. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate04

/-- A rectangular grid large enough for every canonical numerator and denominator.
Natural floors retain the upper boundary even at nonintegral cutoffs. -/
noncomputable def numeratorDenominatorGrid (V : ℝ) : Finset (ℕ × ℕ) :=
  (Finset.range (⌊4 * V⌋₊ + 1)) ×ˢ (Finset.range (⌊2 * V⌋₊ + 1))

/-- Filter the finite image by the actual canonical denominator, not the
possibly unreduced denominator of a grid representative. -/
noncomputable def rationalShell (V : ℝ) : Finset ℚ := by
  classical
  exact ((numeratorDenominatorGrid V).image (fun p => (p.1 : ℚ) / p.2)).filter
    (fun s => 1 ≤ s ∧ s ≤ 2 ∧ V < (s.den : ℝ) ∧ (s.den : ℝ) ≤ 2 * V)

theorem canonical_num_bounds {s : ℚ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) :
    0 ≤ s.num ∧ (s.den : ℝ) ≤ (s.num : ℝ) ∧
      (s.num : ℝ) ≤ 2 * (s.den : ℝ) := by
  have hd : (0 : ℝ) < s.den := by exact_mod_cast s.pos
  have h1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
  have h2 : (s : ℝ) ≤ 2 := by exact_mod_cast hs2
  rw [Rat.cast_def, le_div_iff₀ hd] at h1
  rw [Rat.cast_def, div_le_iff₀ hd] at h2
  exact ⟨Rat.num_nonneg.mpr (by linarith), by simpa using h1, h2⟩

theorem canonical_pair_mem_grid {V : ℝ} {s : ℚ}
    (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (hd : (s.den : ℝ) ≤ 2 * V) :
    (s.num.toNat, s.den) ∈ numeratorDenominatorGrid V := by
  obtain ⟨hn, _, hu⟩ := canonical_num_bounds hs1 hs2
  have he : (s.num.toNat : ℝ) = (s.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hn
  apply Finset.mem_product.mpr
  constructor
  · apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Nat.le_floor (by rw [he]; linarith))
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hd))

theorem mem_rationalShell {V : ℝ} {s : ℚ} :
    s ∈ rationalShell V ↔
      1 ≤ s ∧ s ≤ 2 ∧ V < (s.den : ℝ) ∧ (s.den : ℝ) ≤ 2 * V := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨(s.num.toNat, s.den),
      canonical_pair_mem_grid h.1 h.2.1 h.2.2.2, ?_⟩, h⟩
    have hn := (canonical_num_bounds h.1 h.2.1).1
    have he : (s.num.toNat : ℚ) = (s.num : ℚ) := by
      exact_mod_cast Int.toNat_of_nonneg hn
    simpa only [he] using Rat.num_div_den s

theorem numeratorDenominatorGrid_card_le {V : ℝ} (hV : 1 ≤ V) :
    ((numeratorDenominatorGrid V).card : ℝ) ≤ 15 * V ^ 2 := by
  have h4 := Nat.floor_le (by linarith : 0 ≤ 4 * V)
  have h2 := Nat.floor_le (by linarith : 0 ≤ 2 * V)
  have h4' : (⌊4 * V⌋₊ : ℝ) + 1 ≤ 5 * V := by linarith
  have h2' : (⌊2 * V⌋₊ : ℝ) + 1 ≤ 3 * V := by linarith
  have h := mul_le_mul h4' h2' (by positivity) (by linarith : 0 ≤ 5 * V)
  simp only [numeratorDenominatorGrid, Finset.card_product, Finset.card_range,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  nlinarith [h]

/-- Explicit absolute polynomial bound, uniform over real shell cutoffs. -/
theorem rationalShell_card_le {V : ℝ} (hV : 1 ≤ V) :
    ((rationalShell V).card : ℝ) ≤ 15 * V ^ 2 := by
  classical
  have h : (rationalShell V).card ≤ (numeratorDenominatorGrid V).card :=
    (Finset.card_filter_le _ _).trans Finset.card_image_le
  exact (by exact_mod_cast h : ((rationalShell V).card : ℝ) ≤
    (numeratorDenominatorGrid V).card).trans (numeratorDenominatorGrid_card_le hV)

end ErdosMahlerAudit.Gate04
