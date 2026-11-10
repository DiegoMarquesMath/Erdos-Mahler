module

public import ErdosMahlerAudit.Gate11.Separation
public import ErdosMahlerAudit.Gate10.Successors

/-! Actual admissible successor intervals (frozen TeX 281–327).
The only external mathematical inputs are the two inherited contracts. -/

public section
namespace ErdosMahlerAudit.Gate11

/-- Choose the block after the parent, then order the actual indices returned
by Gate 10. Membership retains every exceptional-denominator condition. -/
theorem ordered_successors
    (hST : Gate05.SubspaceTwoThreePrimitive) (hMatveev : Gate08.MatveevRationalThree)
    (τ : ℝ) (hτ : 4 ≤ τ) :
    ∃ t0 : ℕ, 0 < t0 ∧ ∀ t : ℕ, t0 ≤ t →
      ∃ N : ℕ, N ∈ convergentDenominators ∧ 3 ^ t < N ∧
        ∃ b c : ℕ, b ∈ Gate02.admissibleIndices t τ N ∧
          c ∈ Gate02.admissibleIndices t τ N ∧ t < b ∧ b < c ∧ c < 2 * b := by
  obtain ⟨t0, ht0, hs⟩ := Gate10.two_successors hST hMatveev τ hτ
  refine ⟨t0, ht0, ?_⟩
  intro t ht
  obtain ⟨N, hN, hB, b, hb, c, hc, hne⟩ := hs t ht (max (3 ^ t + 1) (t + 1))
  have hQN : 3 ^ t < N := by
    have := (le_max_left (3 ^ t + 1) (t + 1)).trans hB
    omega
  have htN : t < N := by
    have := (le_max_right (3 ^ t + 1) (t + 1)).trans hB
    omega
  have hordered : ∃ b c : ℕ, b ∈ Gate02.admissibleIndices t τ N ∧
      c ∈ Gate02.admissibleIndices t τ N ∧ b < c := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨b, c, hb, hc, h⟩
    · exact ⟨c, b, hc, hb, h⟩
  obtain ⟨b, c, hb, hc, hbc⟩ := hordered
  have hbN := Gate02.mem_admissibleIndices.mp hb
  have hcN := Gate02.mem_admissibleIndices.mp hc
  exact ⟨N, hN, hQN, b, c, hb, hc, htN.trans_le hbN.1, hbc, by omega⟩

/-- The exact finite branching step: entire closed intervals nest strictly,
are strictly separated, and have strictly contracting widths. This theorem
asserts neither an infinite path nor the Cantor or irrationality-exponent result. -/
theorem nested_disjoint_successor_intervals
    (hST : Gate05.SubspaceTwoThreePrimitive) (hMatveev : Gate08.MatveevRationalThree)
    (τ : ℝ) (hτ : 4 ≤ τ) :
    ∃ t0 : ℕ, 0 < t0 ∧ ∀ t : ℕ, t0 ≤ t →
      K τ t ⊆ Set.Ioo 1 2 ∧
      ∃ N : ℕ, N ∈ convergentDenominators ∧ 3 ^ t < N ∧
        ∃ b c : ℕ, b ∈ Gate02.admissibleIndices t τ N ∧
          c ∈ Gate02.admissibleIndices t τ N ∧
          t < b ∧ b < c ∧ c < 2 * b ∧
          K τ b ⊆ interior (K τ t) ∧ K τ c ⊆ interior (K τ t) ∧
          (right τ b < left τ c ∨ right τ c < left τ b) ∧
          Disjoint (K τ b) (K τ c) ∧
          (right τ b - left τ b ≤ (right τ t - left τ t) / 81 ∧
            right τ b - left τ b < right τ t - left τ t) ∧
          (right τ c - left τ c ≤ (right τ t - left τ t) / 81 ∧
            right τ c - left τ c < right τ t - left τ t) := by
  obtain ⟨t0, ht0, hs⟩ := ordered_successors hST hMatveev τ hτ
  refine ⟨t0, ht0, ?_⟩
  intro t ht
  have htpos := ht0.trans_le ht
  obtain ⟨N, hN, hQN, b, c, hb, hc, htb, hbc, hc2b⟩ := hs t ht
  have htc := htb.trans hbc
  have hbpos := htpos.trans htb
  exact ⟨K_subset_Ioo htpos hτ, N, hN, hQN, b, c, hb, hc, htb, hbc, hc2b,
    K_subset_interior hτ htb (Gate02.mem_admissibleIndices.mp hb).2.2.1,
    K_subset_interior hτ htc (Gate02.mem_admissibleIndices.mp hc).2.2.1,
    strictly_separated hτ hbpos hbc hc2b, K_disjoint hτ hbpos hbc hc2b,
    width_contraction hτ htb, width_contraction hτ htc⟩

end ErdosMahlerAudit.Gate11
