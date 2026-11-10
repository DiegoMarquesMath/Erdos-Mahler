module

public import ErdosMahlerAudit.Gate02.Exceptional

/-! Exact Section 2 intervals, cutoffs, and finite admissible index sets. -/

@[expose] public section

namespace ErdosMahlerAudit.Gate02

noncomputable def radius (t : ℕ) (τ : ℝ) : ℝ := (3 : ℝ) ^ (-τ * (t : ℝ))

noncomputable def J (t : ℕ) (τ : ℝ) : Set ℝ :=
  Set.Ioo ((R t : ℝ) + radius t τ) ((R t : ℝ) + 2 * radius t τ)

noncomputable def nu (t : ℕ) : ℝ := 4 + 1 / (t : ℝ)

noncomputable def cutoff (t : ℕ) (τ : ℝ) : ℝ :=
  ((3 : ℝ) ^ t) ^ (τ - 1) / 6

/-- Endpoint difference for the decreasing map Phi, i.e. the length of its
image interval when J is in the manuscript domain. -/
noncomputable def rho (t : ℕ) (τ : ℝ) : ℝ :=
  Phi ((R t : ℝ) + radius t τ) - Phi ((R t : ℝ) + 2 * radius t τ)

noncomputable def candidateIndices (t : ℕ) (τ : ℝ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico N (2 * N)).filter (fun b => (R b : ℝ) ∈ J t τ)

noncomputable def admissibleIndices (t : ℕ) (τ : ℝ) (N : ℕ) : Finset ℕ :=
  candidateIndices t τ N \ badIndices N (cutoff t τ) (nu t)

theorem radius_pos (t : ℕ) (τ : ℝ) : 0 < radius t τ :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem radius_eq_Q (t : ℕ) (τ : ℝ) :
    radius t τ = ((3 : ℝ) ^ t) ^ (-τ) := by
  rw [radius, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

theorem cutoff_pos (t : ℕ) (τ : ℝ) : 0 < cutoff t τ := by
  unfold cutoff
  positivity

theorem parent_parameters {t : ℕ} (ht : 0 < t) (τ : ℝ) :
    (t : ℝ) ≠ 0 ∧ 4 < nu t ∧ nu t ≤ 5 ∧ 0 < cutoff t τ := by
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have htone : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hinv : 1 / (t : ℝ) ≤ 1 := (div_le_one htpos).mpr htone
  exact ⟨ne_of_gt htpos, lt_add_of_pos_right 4 (div_pos zero_lt_one htpos),
    by dsimp [nu]; linarith, cutoff_pos t τ⟩

theorem mem_candidateIndices {t N b : ℕ} {τ : ℝ} :
    b ∈ candidateIndices t τ N ↔ N ≤ b ∧ b < 2 * N ∧ (R b : ℝ) ∈ J t τ := by
  classical
  simp [candidateIndices, and_assoc]

theorem mem_admissibleIndices {t N b : ℕ} {τ : ℝ} :
    b ∈ admissibleIndices t τ N ↔
      N ≤ b ∧ b < 2 * N ∧ (R b : ℝ) ∈ J t τ ∧
        ∀ s : ℚ, Exceptional b (nu t) s → (s.den : ℝ) ≤ cutoff t τ := by
  classical
  simp only [admissibleIndices, Finset.mem_sdiff, mem_candidateIndices, mem_badIndices]
  constructor
  · rintro ⟨⟨hN, hb, hJ⟩, hbad⟩
    refine ⟨hN, hb, hJ, ?_⟩
    intro s hs
    by_contra hd
    exact hbad ⟨hN, hb, s, hs, lt_of_not_ge hd⟩
  · rintro ⟨hN, hb, hJ, hgood⟩
    refine ⟨⟨hN, hb, hJ⟩, ?_⟩
    rintro ⟨_, _, s, hs, hd⟩
    exact (not_lt_of_ge (hgood s hs)) hd

/-- Natural subtraction: the exact candidate set minus the exact bad set. -/
theorem admissible_card_lower (t N : ℕ) (τ : ℝ) :
    (candidateIndices t τ N).card - E N (cutoff t τ) (nu t) ≤
      (admissibleIndices t τ N).card :=
  Finset.le_card_sdiff _ _

/-- Additive version avoids truncating subtraction when taking real casts. -/
theorem candidate_card_le (t N : ℕ) (τ : ℝ) :
    (candidateIndices t τ N).card ≤
      (admissibleIndices t τ N).card + E N (cutoff t τ) (nu t) :=
  Finset.card_le_card_sdiff_add_card

theorem admissible_card_lower_real (t N : ℕ) (τ : ℝ) :
    ((candidateIndices t τ N).card : ℝ) - (E N (cutoff t τ) (nu t) : ℝ) ≤
      ((admissibleIndices t τ N).card : ℝ) := by
  have h : ((candidateIndices t τ N).card : ℝ) ≤
      ((admissibleIndices t τ N).card : ℝ) + (E N (cutoff t τ) (nu t) : ℝ) := by
    exact_mod_cast candidate_card_le t N τ
  linarith

theorem admissible_index_positive {t N b : ℕ} {τ : ℝ}
    (hN : 0 < N) (hb : b ∈ admissibleIndices t τ N) : 0 < b :=
  hN.trans_le (mem_admissibleIndices.mp hb).1

theorem admissible_approximation_lower {t N b : ℕ} {τ : ℝ}
    (ht : 0 < t) (hN : 0 < N) (hb : b ∈ admissibleIndices t τ N)
    (s : ℚ) (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (hne : s ≠ R b)
    (hd : cutoff t τ < (s.den : ℝ)) :
    1 / (16 * (s.den : ℝ) ^ nu t) ≤ |(R b : ℝ) - (s : ℝ)| := by
  by_contra herr
  have hp := parent_parameters ht τ
  have he : Exceptional b (nu t) s :=
    ⟨admissible_index_positive hN hb, hp.2.1, hp.2.2.1,
      hs1, hs2, hne, lt_of_not_ge herr⟩
  exact (not_lt_of_ge ((mem_admissibleIndices.mp hb).2.2.2 s he)) hd

end ErdosMahlerAudit.Gate02
