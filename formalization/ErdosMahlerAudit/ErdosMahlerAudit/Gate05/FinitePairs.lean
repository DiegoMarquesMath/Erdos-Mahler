module

public import ErdosMahlerAudit.Gate05.ExternalContract
public import ErdosMahlerAudit.Gate05.HeightEstimates
public import Mathlib.Data.Set.Finite.Lattice

/-! Finiteness and separation concern primitive pairs, not indices or witnesses. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate05

noncomputable def smallProductPairs (ε : ℝ) : Set (ℕ × ℕ) :=
  {z | 0 < z.1 ∧ 0 < z.2 ∧ Nat.Coprime z.1 z.2 ∧
    localProduct z.1 z.2 < (2 : ℝ) ^ (1 + ε / 2) * (max z.1 z.2 : ℕ) ^ (-ε / 2)}

theorem smallProductPairs_finite (hST : SubspaceTwoThreePrimitive)
    {ε : ℝ} (hε : 0 < ε) : (smallProductPairs ε).Finite := by
  obtain ⟨M, _, hM⟩ := exists_euclidean_threshold hε
  obtain ⟨K, hK⟩ := exists_nat_ge M
  let box := (Finset.range (K + 1)) ×ˢ (Finset.range (K + 1))
  let δ := min (ε / 4) (1 / 2 : ℝ)
  have hd := delta_bounds hε
  apply (box.finite_toSet.union (hST δ hd.1 hd.2.1)).subset
  intro z hz
  obtain ⟨hx, hy, hcop, hprod⟩ := hz
  by_cases hlarge : M ≤ (max z.1 z.2 : ℕ)
  · right
    refine ⟨hx, hy, hcop, hprod.trans ?_⟩
    simpa only [Nat.cast_max] using hM (z.1 : ℝ) (z.2 : ℝ)
      (by exact_mod_cast hx) (by exact_mod_cast hy) (by simpa using hlarge)
  · left
    have hzK : max z.1 z.2 ≤ K := by
      exact_mod_cast (lt_of_not_ge hlarge).le.trans hK
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr
      (Nat.lt_succ_of_le ((le_max_left _ _).trans hzK)),
      Finset.mem_range.mpr (Nat.lt_succ_of_le ((le_max_right _ _).trans hzK))⟩

theorem violating_pair_mem {b : ℕ} {s : ℚ} {ε : ℝ}
    (hb : 0 < b) (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (hε : 0 < ε) (hne : s ≠ R b)
    (herr : |(R b : ℝ) - s| < (S b : ℝ) ^ (-ε) * (v s : ℝ) ^ (-2 : ℝ)) :
    (U b s, W b s) ∈ smallProductPairs ε := by
  refine ⟨U_pos b s, W_pos b hs1, UW_coprime b s, ?_⟩
  have hH : (0 : ℝ) < H b s := by
    exact_mod_cast (lt_of_lt_of_le (U_pos b s) (le_max_left _ _))
  exact (violation_product_lt hb hs1 hs2 herr).trans_le
    (scale_power_bound hH (by exact_mod_cast S_pos b) hε
      (violation_height_lt hb hs1 hs2 hε hne herr).le)

/-- The diagonal is explicitly excluded; the finite set itself may contain it. -/
theorem finite_pair_gap (T : Set (ℕ × ℕ)) (hT : T.Finite) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ z ∈ T, 0 < z.2 → z.1 ≠ z.2 →
      γ ≤ |(z.1 : ℝ) / z.2 - 1| := by
  obtain ⟨K, hK⟩ := (hT.image Prod.snd).bddAbove
  refine ⟨1 / ((K : ℝ) + 1), by positivity, ?_⟩
  intro z hz hy hne
  have hyR : (0 : ℝ) < z.2 := by exact_mod_cast hy
  have hzK : (z.2 : ℝ) ≤ (K : ℝ) + 1 := by
    have h : z.2 ≤ K := hK ⟨z, hz, rfl⟩
    have : (z.2 : ℝ) ≤ K := by exact_mod_cast h
    linarith
  have hdiff : (1 : ℝ) ≤ |(z.1 : ℝ) - z.2| := by
    have hn : (z.1 : ℤ) - z.2 ≠ 0 := by
      intro h; exact hne (by exact_mod_cast sub_eq_zero.mp h)
    exact_mod_cast Int.one_le_abs hn
  have hid : (z.1 : ℝ) / z.2 - 1 = ((z.1 : ℝ) - z.2) / z.2 := by field_simp
  rw [hid, abs_div, abs_of_pos hyR]
  exact (one_div_le_one_div_of_le hyR hzK).trans
    (div_le_div_of_nonneg_right hdiff hyR.le)

end ErdosMahlerAudit.Gate05
