module

public import ErdosMahlerAudit.Gate04.DyadicDecomposition

/-! Count the exact denominator range (D,U], using finite truncated shells. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate04
open scoped BigOperators

noncomputable def boundedIndices (N : ℕ) (D U ν : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Ico N (2 * N)).filter (fun b =>
    ∃ s : ℚ, Exceptional b ν s ∧ D < (s.den : ℝ) ∧ (s.den : ℝ) ≤ U)

theorem boundedIndices_empty {N : ℕ} {D U ν : ℝ} (hUD : U ≤ D) :
    boundedIndices N D U ν = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  obtain ⟨_, s, _, hlo, hhi⟩ := Finset.mem_filter.mp hb
  exact (not_lt_of_ge (hhi.trans hUD)) hlo

/-- The final shell is explicitly intersected with the closed cutoff at U.
All real cutoffs, including U≤D, are allowed. -/
theorem boundedIndices_eq_truncated_union {N k : ℕ} {D U ν : ℝ}
    (hD : 0 < D) (hUk : U ≤ dyadicScale D k) :
    boundedIndices N D U ν = (Finset.range k).biUnion (fun i =>
      boundedIndices N (dyadicScale D i) (min (2 * dyadicScale D i) U) ν) := by
  classical
  ext b
  simp only [boundedIndices, Finset.mem_filter, Finset.mem_biUnion]
  constructor
  · rintro ⟨hb, s, hs, hd, hu⟩
    obtain ⟨i, hi, hlo, hhi⟩ := dyadic_cover hd hu hUk
    exact ⟨i, hi, hb, s, hs, hlo, hhi⟩
  · rintro ⟨i, _, hb, s, hs, hlo, hhi⟩
    exact ⟨hb, s, hs, (le_dyadicScale hD.le i).trans_lt hlo,
      hhi.trans (min_le_right _ _)⟩

theorem truncatedIndices_subset_shell (N : ℕ) (V U ν : ℝ) :
    boundedIndices N V (min (2 * V) U) ν ⊆ shellIndices N V ν := by
  classical
  intro b hb
  obtain ⟨hb, s, hs, hlo, hhi⟩ := Finset.mem_filter.mp hb
  exact Finset.mem_filter.mpr ⟨hb, s, hs, hlo, hhi.trans (min_le_left _ _)⟩

/-- The finite cover gives an upper bound by full-shell counts. No disjointness
of witnesses or index sets is assumed. -/
theorem boundedIndices_card_le_sum {N k : ℕ} {D U ν : ℝ}
    (hD : 0 < D) (hUk : U ≤ dyadicScale D k) :
    (boundedIndices N D U ν).card ≤
      ∑ i ∈ Finset.range k, (shellIndices N (dyadicScale D i) ν).card := by
  classical
  rw [boundedIndices_eq_truncated_union hD hUk]
  exact Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun i _ =>
    Finset.card_le_card (truncatedIndices_subset_shell N (dyadicScale D i) U ν)))

/-- Absolute small-range bound. No ν-dependent constant or height threshold;
U is an arbitrary real number, so equality and reversed cutoffs are included. -/
theorem boundedIndices_card_le {N : ℕ} (hN : N ∈ convergentDenominators)
    {D U ν : ℝ} (hD : 2 ≤ D) (hν : 4 ≤ ν) :
    ((boundedIndices N D U ν).card : ℝ) ≤
      60 * ((N : ℝ) * D ^ (2 - ν) + U ^ 2) := by
  classical
  have hDp : 0 < D := by linarith
  obtain ⟨k, hUk, hactive⟩ := exists_dyadic_cutoff (U := U) hDp
  have hcover : ((boundedIndices N D U ν).card : ℝ) ≤
      ∑ i ∈ Finset.range k, ((shellIndices N (dyadicScale D i) ν).card : ℝ) := by
    exact_mod_cast boundedIndices_card_le_sum (N := N) (ν := ν) hDp hUk
  have hsum : (∑ i ∈ Finset.range k,
      ((shellIndices N (dyadicScale D i) ν).card : ℝ)) ≤
      45 * ((N : ℝ) * (∑ i ∈ Finset.range k, (dyadicScale D i) ^ (2 - ν)) +
        ∑ i ∈ Finset.range k, (dyadicScale D i) ^ 2) := by
    calc
      _ ≤ ∑ i ∈ Finset.range k,
          45 * ((N : ℝ) * (dyadicScale D i) ^ (2 - ν) + (dyadicScale D i) ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        exact shellIndices_card_le hN (hD.trans (le_dyadicScale hDp.le i)) (by linarith)
      _ = _ := by simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have hneg := mul_le_mul_of_nonneg_left (dyadic_negative_sum hDp hν k) (Nat.cast_nonneg N)
  have hpos := dyadic_square_sum hDp k hactive
  have htotal := hcover.trans hsum
  nlinarith

/-- Splitting witnesses, rather than subtracting natural-valued counts. -/
theorem E_le_high_add_bounded (N : ℕ) (D U ν : ℝ) :
    Gate02.E N D ν ≤ Gate02.E N U ν + (boundedIndices N D U ν).card := by
  classical
  have hcover : Gate02.badIndices N D ν ⊆
      Gate02.badIndices N U ν ∪ boundedIndices N D U ν := by
    intro b hb
    obtain ⟨hNb, hbN, s, hs, hd⟩ := Gate02.mem_badIndices.mp hb
    by_cases hu : U < (s.den : ℝ)
    · exact Finset.mem_union_left _ (Gate02.mem_badIndices.mpr ⟨hNb, hbN, s, hs, hu⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr ⟨hNb, hbN⟩, s, hs, hd, le_of_not_gt hu⟩)
  exact (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)

end ErdosMahlerAudit.Gate04
