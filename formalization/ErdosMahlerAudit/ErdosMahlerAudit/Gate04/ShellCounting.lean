module

public import ErdosMahlerAudit.Gate04.RationalGrid
public import ErdosMahlerAudit.Gate04.Neighborhood
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Finite witness unions for TeX lines 513–514. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate04
open scoped BigOperators

noncomputable def shellIndices (N : ℕ) (V ν : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Ico N (2 * N)).filter (fun b =>
    ∃ s : ℚ, Exceptional b ν s ∧ V < (s.den : ℝ) ∧ (s.den : ℝ) ≤ 2 * V)

/-- Equality of finite sets, retaining duplicate witnesses only in the union. -/
theorem shellIndices_eq_biUnion (N : ℕ) (V ν : ℝ) :
    shellIndices N V ν = (rationalShell V).biUnion (witnessIndices N ν) := by
  classical
  ext b
  simp only [shellIndices, witnessIndices, Finset.mem_filter, Finset.mem_biUnion]
  constructor
  · rintro ⟨hb, s, hs, hv, hv'⟩
    exact ⟨s, mem_rationalShell.mpr ⟨hs.2.2.2.1, hs.2.2.2.2.1, hv, hv'⟩, hb, hs⟩
  · rintro ⟨s, hs, hb, he⟩
    exact ⟨hb, s, he, (mem_rationalShell.mp hs).2.2⟩

/-- Finite union bound: indices with several witnesses are not counted as
distinct indices in the left side. -/
theorem shellIndices_card_le_sum (N : ℕ) (V ν : ℝ) :
    (shellIndices N V ν).card ≤
      ∑ s ∈ rationalShell V, (witnessIndices N ν s).card := by
  classical
  rw [shellIndices_eq_biUnion]
  exact Finset.card_biUnion_le

/-- One absolute coefficient for every real shell cutoff and exponent ≥0. -/
theorem shellIndices_card_le {N : ℕ} (hN : N ∈ convergentDenominators)
    {V ν : ℝ} (hV : 2 ≤ V) (hν : 0 ≤ ν) :
    ((shellIndices N V ν).card : ℝ) ≤
      45 * ((N : ℝ) * V ^ (2 - ν) + V ^ 2) := by
  classical
  have hVp : 0 < V := by linarith
  have hsum : ((shellIndices N V ν).card : ℝ) ≤
      ∑ s ∈ rationalShell V, ((witnessIndices N ν s).card : ℝ) := by
    exact_mod_cast shellIndices_card_le_sum N V ν
  have hterms : (∑ s ∈ rationalShell V, ((witnessIndices N ν s).card : ℝ)) ≤
      (rationalShell V).card * ((N : ℝ) * V ^ (-ν) + 3) := by
    calc
      _ ≤ ∑ _s ∈ rationalShell V, ((N : ℝ) * V ^ (-ν) + 3) := by
        apply Finset.sum_le_sum
        intro s hs
        obtain ⟨hs1, hs2, hv, _⟩ := mem_rationalShell.mp hs
        exact witnessIndices_card_le_shell hN hs1 hs2 hν hVp hv
      _ = _ := by simp; ring
  have hgrid := mul_le_mul_of_nonneg_right (rationalShell_card_le (by linarith : 1 ≤ V))
    (by positivity : 0 ≤ (N : ℝ) * V ^ (-ν) + 3)
  have he : V ^ (2 - ν) = V ^ 2 * V ^ (-ν) := by
    rw [sub_eq_add_neg, Real.rpow_add hVp, Real.rpow_two]
  have hp : 0 ≤ (N : ℝ) * V ^ (2 - ν) := by positivity
  calc
    _ ≤ 15 * V ^ 2 * ((N : ℝ) * V ^ (-ν) + 3) := hsum.trans (hterms.trans hgrid)
    _ = 15 * ((N : ℝ) * V ^ (2 - ν)) + 45 * V ^ 2 := by rw [he]; ring
    _ ≤ _ := by nlinarith

end ErdosMahlerAudit.Gate04
