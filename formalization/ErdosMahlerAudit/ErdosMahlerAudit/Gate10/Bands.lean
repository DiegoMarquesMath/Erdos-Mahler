module

public import ErdosMahlerAudit.Gate10.Scales

/-! Actual witness coverage, zero height, active tails, and finite coverage.
These are the obligations at TeX 1026–1049 and 1061–1077. -/

public section
namespace ErdosMahlerAudit.Gate10
open scoped BigOperators

/-- The strict cube-root cutoff excludes denominator one even at N=1. -/
theorem high_denominator_log_pos {N : ℕ} {s : ℚ} (hN : 0 < N)
    (hs : (N : ℝ) ^ (1 / 3 : ℝ) < (s.den : ℝ)) : 0 < Real.log (s.den : ℝ) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact Real.log_pos ((Real.one_le_rpow hN1 (by norm_num)).trans_lt hs)

/-- Zero height excludes high witnesses, not all exceptional witnesses. -/
theorem high_count_zero_of_height_zero {N : ℕ} {ν : ℝ} (hN : 0 < N)
    (hW : Gate05.logarithmicHeight N ν = 0) :
    Gate02.E N ((N : ℝ) ^ (1 / 3 : ℝ)) ν = 0 := by
  classical
  have he : Gate02.badIndices N ((N : ℝ) ^ (1 / 3 : ℝ)) ν = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro b hb
    obtain ⟨hb, hb2, s, hs, hd⟩ := Gate02.mem_badIndices.mp hb
    have hl := Gate05.witness_log_le_height hb hb2 hs
    rw [hW] at hl
    exact (not_lt_of_ge hl) (high_denominator_log_pos hN hd)
  simp only [Gate02.E, he, Finset.card_empty]

/-- Coverage retains both lower cutoffs in the exact Gate06 band. -/
theorem high_witness_covered {N b : ℕ} {ν θ : ℝ} {s : ℚ}
    (hN : 0 < N) (hθ : 1 < θ) (hb : N ≤ b) (hb2 : b < 2 * N)
    (hs : Exceptional b ν s) (hd : (N : ℝ) ^ (1 / 3 : ℝ) < (s.den : ℝ))
    (hW : Gate05.logarithmicHeight N ν ≤ (N : ℝ)) :
    ∃ j : ℕ, b ∈ Gate06.exceptionalBand N ν θ (heightScale N θ j) := by
  have hv : (0 : ℝ) < s.den := by exact_mod_cast s.pos
  obtain ⟨j, hj, hj'⟩ := heightScale_cover hN hθ (high_denominator_log_pos hN hd)
    ((Gate05.witness_log_le_height hb hb2 hs).trans hW)
  refine ⟨j, Gate06.mem_exceptionalBand.mpr ⟨hb, hb2, s, hs, ?_, ?_⟩⟩
  · exact max_lt ((Real.lt_log_iff_exp_lt hv).mp hj) hd
  · exact (Real.log_le_iff_le_exp hv).mp hj'

/-- The actual witness supplies both strict inequalities for active heights. -/
theorem activeBand_bounds {N : ℕ} {ν θ w : ℝ} (hN : 0 < N) (hθ : 1 < θ)
    (hA : (Gate06.exceptionalBand N ν θ w).Nonempty) :
    (1 / 3 : ℝ) * Real.log (N : ℝ) < w ∧ w < θ * Gate05.logarithmicHeight N ν := by
  obtain ⟨b, hb⟩ := hA
  obtain ⟨hb, hb2, s, hs, hd, hu⟩ := Gate06.mem_exceptionalBand.mp hb
  have hv : (0 : ℝ) < s.den := by exact_mod_cast s.pos
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hlo := Real.log_lt_log (Real.rpow_pos_of_pos hNr (1 / 3))
    ((le_max_right _ _).trans_lt hd)
  rw [Real.log_rpow hNr] at hlo
  have hhi : Real.log (s.den : ℝ) ≤ w := (Real.log_le_iff_le_exp hv).mpr hu
  have hlow : w / θ < Real.log (s.den : ℝ) :=
    (Real.lt_log_iff_exp_lt hv).mpr ((le_max_left _ _).trans_lt hd)
  have hw : w < θ * Real.log (s.den : ℝ) := by
    have := (div_lt_iff₀ (by linarith : 0 < θ)).mp hlow
    linarith
  exact ⟨hlo.trans_le hhi, hw.trans_le (mul_le_mul_of_nonneg_left
    (Gate05.witness_log_le_height hb hb2 hs) (by linarith))⟩

/-- Gate05 sublinearity, at a fixed positive tolerance, supplies the global cover. -/
theorem eventually_height_lt_N (hST : Gate05.SubspaceTwoThreePrimitive)
    {ν : ℝ} (hν : 4 < ν) (hν5 : ν ≤ 5) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → N ∈ convergentDenominators →
      Gate05.logarithmicHeight N ν < (N : ℝ) := by
  obtain ⟨N0, hN0⟩ := Gate05.logarithmicHeight_sublinear hST ν hν hν5
    (1 / 2) (by norm_num)
  refine ⟨N0, ?_⟩
  intro N hN hND
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr (Gate03.convergentDenominators_pos hND)
  have := hN0 N hN hND
  linarith

/-- For fixed J, every active band eventually lies at or beyond J.
No rate of sublinearity is required. θ and J are fixed before N0. -/
theorem eventually_active_ge (hST : Gate05.SubspaceTwoThreePrimitive)
    {ν θ : ℝ} (hν : 4 < ν) (hν5 : ν ≤ 5) (hθ : 1 < θ) (J : ℕ) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → N ∈ convergentDenominators →
      ∀ j : ℕ, (Gate06.exceptionalBand N ν θ (heightScale N θ j)).Nonempty → J ≤ j := by
  have hθ0 : 0 < θ := by linarith
  obtain ⟨N0, hN0⟩ := Gate05.logarithmicHeight_sublinear hST ν hν hν5
    (1 / (θ * θ ^ J)) (by positivity)
  refine ⟨N0, ?_⟩
  intro N hN hND j hj
  have hu := (activeBand_bounds (Gate03.convergentDenominators_pos hND) hθ hj).2
  have hW := mul_le_mul_of_nonneg_left (hN0 N hN hND) hθ0.le
  have he : θ * (1 / (θ * θ ^ J) * (N : ℝ)) = heightScale N θ J := by
    dsimp [heightScale]
    field_simp
  rw [he] at hW
  by_contra h
  have hm := heightScale_antitone N hθ (Nat.le_of_lt (Nat.lt_of_not_ge h))
  linarith

/-- A fixed absolute N cutoff makes every active height at least one. -/
theorem eventually_active_height_ge_one :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ ν θ w : ℝ, 1 < θ →
      (Gate06.exceptionalBand N ν θ w).Nonempty → 1 ≤ w := by
  obtain ⟨N0, hN0⟩ := exists_nat_gt (Real.exp 3)
  refine ⟨N0, ?_⟩
  intro N hN ν θ w hθ hA
  have hNr : Real.exp 3 < (N : ℝ) := hN0.trans_le (Nat.cast_le.mpr hN)
  have hNp : 0 < N := Nat.cast_pos.mp ((Real.exp_pos 3).trans hNr)
  have hl : 3 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt (Nat.cast_pos.mpr hNp)).mpr hNr
  have hw := (activeBand_bounds hNp hθ hA).1
  linarith

/-- For N>1 there are only finitely many active bands. The bound comes from
an ordinary power exceeding N / ((log N)/3), never an extremum of active indices. -/
theorem activeBands_finite_range {N : ℕ} {ν θ : ℝ} (hN : 1 < N) (hθ : 1 < θ) :
    ∃ K : ℕ, ∀ j : ℕ,
      (Gate06.exceptionalBand N ν θ (heightScale N θ j)).Nonempty → j < K := by
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  obtain ⟨K, hK⟩ := heightScale_finite_cutoff N hθ
    (show 0 < (1 / 3 : ℝ) * Real.log (N : ℝ) by positivity)
  exact ⟨K, fun j hj => hK j (activeBand_bounds (by omega) hθ hj).1.le⟩

/-- A finite union of the actual bands covers every high exceptional index.
Multiple rational witnesses for the same index cause no injectivity assumption. -/
theorem high_count_le_finite_band_sum {N : ℕ} {ν θ : ℝ} (hN : 1 < N) (hθ : 1 < θ)
    (hW : Gate05.logarithmicHeight N ν ≤ (N : ℝ)) :
    ∃ K : ℕ, Gate02.E N ((N : ℝ) ^ (1 / 3 : ℝ)) ν ≤
      ∑ j ∈ Finset.range K, (Gate06.exceptionalBand N ν θ (heightScale N θ j)).card := by
  classical
  obtain ⟨K, hK⟩ := activeBands_finite_range (ν := ν) hN hθ
  refine ⟨K, ?_⟩
  have hsub : Gate02.badIndices N ((N : ℝ) ^ (1 / 3 : ℝ)) ν ⊆
      (Finset.range K).biUnion (fun j => Gate06.exceptionalBand N ν θ (heightScale N θ j)) := by
    intro b hb
    obtain ⟨hb, hb2, s, hs, hd⟩ := Gate02.mem_badIndices.mp hb
    obtain ⟨j, hj⟩ := high_witness_covered (by omega) hθ hb hb2 hs hd hW
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr (hK j ⟨b, hj⟩), hj⟩
  exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

/-- Integrality of the canonical denominator yields a positive height cutoff
for every active band, even for N=1. At N=0 the premise is empty. -/
theorem activeBand_height_ge_log_two {N : ℕ} {ν θ w : ℝ}
    (hA : (Gate06.exceptionalBand N ν θ w).Nonempty) : Real.log 2 ≤ w := by
  obtain ⟨b, hb⟩ := hA
  obtain ⟨hb, hb2, s, _, hd, hu⟩ := Gate06.mem_exceptionalBand.mp hb
  have hN : 0 < N := by omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hd1 : (1 : ℝ) < s.den := (Real.one_le_rpow hN1 (by norm_num)).trans_lt
    ((le_max_right _ _).trans_lt hd)
  have hd2 : (2 : ℝ) ≤ s.den := by
    have : 1 < s.den := by exact_mod_cast hd1
    exact_mod_cast (show 2 ≤ s.den by omega)
  exact (Real.log_le_log (by norm_num) hd2).trans
    ((Real.log_le_iff_le_exp (by exact_mod_cast s.pos)).mpr hu)

/-- Finite activity for every natural N, without an empty-set extremum. -/
theorem activeBands_finite_range_all (N : ℕ) (ν : ℝ) {θ : ℝ} (hθ : 1 < θ) :
    ∃ K : ℕ, ∀ j : ℕ,
      (Gate06.exceptionalBand N ν θ (heightScale N θ j)).Nonempty → j < K := by
  obtain ⟨K, hK⟩ := heightScale_finite_cutoff N hθ (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  exact ⟨K, fun j hj => hK j (activeBand_height_ge_log_two hj)⟩

end ErdosMahlerAudit.Gate10
