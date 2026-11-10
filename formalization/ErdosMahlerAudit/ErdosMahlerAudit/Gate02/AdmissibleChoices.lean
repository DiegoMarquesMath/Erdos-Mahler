module

public import ErdosMahlerAudit.Gate02.FiniteCounting
public import ErdosMahlerAudit.Gate02.Density

/-! Conditional quantitative bridge. The rotation and counting estimates are
ordinary hypotheses on the actual sets; neither estimate is proved here. -/

public section

namespace ErdosMahlerAudit.Gate02

/-- The parent is fixed before the counting threshold is selected. `Crot` is
uniform in parents and block sizes, and `Ccount` is uniform in ν and D.
Unboundedness is unnecessary for this eventual assertion; the next theorem
uses it to obtain actual blocks arbitrarily far out. -/
theorem eventually_two_admissible
    (Dset : Set ℕ) (τ Crot Ccount : ℝ)
    (hrotation : ∀ t : ℕ, 0 < t → ∀ N : ℕ, N ∈ Dset →
      |((candidateIndices t τ N).card : ℝ) - (N : ℝ) * rho t τ| ≤ Crot)
    (hcount : ∀ ν : ℝ, 4 < ν → ν ≤ 5 → ∀ D : ℝ, 2 ≤ D →
      ∀ η : ℝ, 0 < η → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → N ∈ Dset →
        (E N D ν : ℝ) / (N : ℝ) ≤ Ccount * D ^ (2 - ν) + η)
    (_hCcount : 0 < Ccount)
    (t : ℕ) (ht : 0 < t) (hD : 2 ≤ cutoff t τ)
    (hgap : Ccount * (cutoff t τ) ^ (2 - nu t) < rho t τ) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → N ∈ Dset →
      2 ≤ (admissibleIndices t τ N).card := by
  let δ := (rho t τ - Ccount * (cutoff t τ) ^ (2 - nu t)) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hp := parent_parameters ht τ
  obtain ⟨M, hM⟩ := hcount (nu t) hp.2.1 hp.2.2.1 (cutoff t τ) hD δ hδ
  obtain ⟨K, hK⟩ := exists_nat_ge ((Crot + 2) / δ)
  refine ⟨max M (max K 1), ?_⟩
  intro N hN hND
  have hMN : M ≤ N := le_trans (le_max_left _ _) hN
  have hKN : K ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one
    (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hlarge : Crot + 2 ≤ (N : ℝ) * δ := by
    apply (div_le_iff₀ hδ).mp
    exact hK.trans (by exact_mod_cast hKN)
  have hbad := (div_le_iff₀ hNr).mp (hM N hMN hND)
  have hrot := (abs_le.mp (hrotation t ht N hND)).1
  have hfinite := admissible_card_lower_real t N τ
  have htwo : (2 : ℝ) ≤ (admissibleIndices t τ N).card := by
    dsimp [δ] at hbad hlarge
    nlinarith
  exact_mod_cast htwo

/-- Unboundedness is an explicit input, not an inference from membership in an
arbitrary set. Specialize Dset to Gate 01's `convergentDenominators` for the paper. -/
theorem arbitrarily_large_two_admissible
    (Dset : Set ℕ) (τ Crot Ccount : ℝ)
    (hunbounded : ∀ B : ℕ, ∃ N : ℕ, N ∈ Dset ∧ B ≤ N)
    (hrotation : ∀ t : ℕ, 0 < t → ∀ N : ℕ, N ∈ Dset →
      |((candidateIndices t τ N).card : ℝ) - (N : ℝ) * rho t τ| ≤ Crot)
    (hcount : ∀ ν : ℝ, 4 < ν → ν ≤ 5 → ∀ D : ℝ, 2 ≤ D →
      ∀ η : ℝ, 0 < η → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → N ∈ Dset →
        (E N D ν : ℝ) / (N : ℝ) ≤ Ccount * D ^ (2 - ν) + η)
    (hCcount : 0 < Ccount)
    (t : ℕ) (ht : 0 < t) (hD : 2 ≤ cutoff t τ)
    (hgap : Ccount * (cutoff t τ) ^ (2 - nu t) < rho t τ) :
    ∀ B : ℕ, ∃ N : ℕ, N ∈ Dset ∧ B ≤ N ∧
      ∃ b ∈ admissibleIndices t τ N, ∃ c ∈ admissibleIndices t τ N, b ≠ c := by
  obtain ⟨M, hM⟩ := eventually_two_admissible Dset τ Crot Ccount
    hrotation hcount hCcount t ht hD hgap
  intro B
  obtain ⟨N, hND, hN⟩ := hunbounded (max M B)
  refine ⟨N, hND, (le_max_right _ _).trans hN, ?_⟩
  apply Finset.one_lt_card.mp
  exact hM N ((le_max_left _ _).trans hN) hND

/-- Lemma 2.3 in full, conditional on the two uniform estimates, specialized
to the unchanged Gate 01 convergent-denominator set. The density gap and
parent-domain conditions have been discharged, including at τ=4. -/
theorem conditional_admissible_choices
    (τ : ℝ) (hτ : 4 ≤ τ)
    (hrotation : ∃ Crot : ℝ, 0 ≤ Crot ∧
      ∀ t : ℕ, 0 < t → ∀ N : ℕ, N ∈ convergentDenominators →
        |((candidateIndices t τ N).card : ℝ) - (N : ℝ) * rho t τ| ≤ Crot)
    (hcount : ∃ Ccount : ℝ, 0 < Ccount ∧
      ∀ ν : ℝ, 4 < ν → ν ≤ 5 → ∀ D : ℝ, 2 ≤ D →
        ∀ η : ℝ, 0 < η → ∃ N0 : ℕ, ∀ N : ℕ,
          N0 ≤ N → N ∈ convergentDenominators →
            (E N D ν : ℝ) / (N : ℝ) ≤ Ccount * D ^ (2 - ν) + η) :
    ∃ t0 : ℕ, 0 < t0 ∧ ∀ t : ℕ, t0 ≤ t →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → N ∈ convergentDenominators →
        2 ≤ (admissibleIndices t τ N).card := by
  obtain ⟨Crot, _, hrot⟩ := hrotation
  obtain ⟨Ccount, hCcount, hcnt⟩ := hcount
  obtain ⟨t0, ht0, hgap⟩ := eventually_density_gap Ccount hCcount
  refine ⟨t0, ht0, ?_⟩
  intro t ht
  have htpos := ht0.trans_le ht
  exact eventually_two_admissible convergentDenominators τ Crot Ccount hrot hcnt
    hCcount t htpos (cutoff_ge_two htpos hτ) (hgap t ht τ hτ)

/-- Nonvacuous successor selection at arbitrarily large heights. Unboundedness
of the actual convergent denominators is deliberately left as a visible input. -/
theorem conditional_successors
    (τ : ℝ) (hτ : 4 ≤ τ)
    (hunbounded : ∀ B : ℕ, ∃ N : ℕ, N ∈ convergentDenominators ∧ B ≤ N)
    (hrotation : ∃ Crot : ℝ, 0 ≤ Crot ∧
      ∀ t : ℕ, 0 < t → ∀ N : ℕ, N ∈ convergentDenominators →
        |((candidateIndices t τ N).card : ℝ) - (N : ℝ) * rho t τ| ≤ Crot)
    (hcount : ∃ Ccount : ℝ, 0 < Ccount ∧
      ∀ ν : ℝ, 4 < ν → ν ≤ 5 → ∀ D : ℝ, 2 ≤ D →
        ∀ η : ℝ, 0 < η → ∃ N0 : ℕ, ∀ N : ℕ,
          N0 ≤ N → N ∈ convergentDenominators →
            (E N D ν : ℝ) / (N : ℝ) ≤ Ccount * D ^ (2 - ν) + η) :
    ∃ t0 : ℕ, 0 < t0 ∧ ∀ t : ℕ, t0 ≤ t → ∀ B : ℕ,
      ∃ N : ℕ, N ∈ convergentDenominators ∧ B ≤ N ∧
        ∃ b ∈ admissibleIndices t τ N, ∃ c ∈ admissibleIndices t τ N, b ≠ c := by
  obtain ⟨t0, ht0, hparents⟩ := conditional_admissible_choices τ hτ hrotation hcount
  refine ⟨t0, ht0, ?_⟩
  intro t ht B
  obtain ⟨M, hM⟩ := hparents t ht
  obtain ⟨N, hND, hN⟩ := hunbounded (max M B)
  refine ⟨N, hND, (le_max_right _ _).trans hN, ?_⟩
  exact Finset.one_lt_card.mp (hM N ((le_max_left _ _).trans hN) hND)

end ErdosMahlerAudit.Gate02
