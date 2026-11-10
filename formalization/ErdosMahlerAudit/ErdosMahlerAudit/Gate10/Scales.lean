module

public import ErdosMahlerAudit.Gate05.LogarithmicHeight
public import ErdosMahlerAudit.Gate06.Band

/-! Exact adjacent half-open logarithmic bands, TeX 1019–1030. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate10

noncomputable def chosenTheta (ν : ℝ) : ℝ := 1 + (ν - 4) / 8

theorem chosenTheta_admissible {ν : ℝ} (hν : 4 < ν) :
    1 < chosenTheta ν ∧ chosenTheta ν < ν / 4 := by
  dsimp [chosenTheta]
  constructor <;> linarith

/-- Natural powers are used for arithmetic; `heightScale_eq_rpow` identifies
this with precisely N θ^(-j) in the manuscript. -/
noncomputable def heightScale (N : ℕ) (θ : ℝ) (j : ℕ) : ℝ := (N : ℝ) / θ ^ j

theorem heightScale_eq_rpow (N : ℕ) {θ : ℝ} (hθ : 0 < θ) (j : ℕ) :
    heightScale N θ j = (N : ℝ) * θ ^ (-(j : ℝ)) := by
  rw [Real.rpow_neg hθ.le, Real.rpow_natCast]
  rfl

theorem heightScale_zero (N : ℕ) (θ : ℝ) : heightScale N θ 0 = N := by
  simp [heightScale]

theorem heightScale_pos {N : ℕ} {θ : ℝ} (hN : 0 < N) (hθ : 0 < θ) (j : ℕ) :
    0 < heightScale N θ j := div_pos (Nat.cast_pos.mpr hN) (pow_pos hθ j)

theorem heightScale_succ (N : ℕ) (θ : ℝ) (j : ℕ) :
    heightScale N θ (j + 1) = heightScale N θ j / θ := by
  simp only [heightScale, pow_succ, div_div]

theorem heightScale_antitone (N : ℕ) {θ : ℝ} (hθ : 1 < θ) :
    Antitone (heightScale N θ) := by
  intro i j hij
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg N) (pow_pos (by linarith) i)
    (pow_le_pow_right₀ hθ.le hij)

theorem heightScale_log_ratio {N : ℕ} {θ : ℝ} (hN : 0 < N) (hθ : 0 < θ) (j : ℕ) :
    Real.log ((N : ℝ) / heightScale N θ j) = (j : ℝ) * Real.log θ := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have he : (N : ℝ) / heightScale N θ j = θ ^ j := by
    dsimp [heightScale]
    field_simp
  rw [he, Real.log_pow]

/-- Coverage with the strict lower endpoint and inclusive upper endpoint. -/
theorem heightScale_cover {N : ℕ} {θ t : ℝ} (_hN : 0 < N) (hθ : 1 < θ)
    (ht : 0 < t) (htN : t ≤ N) :
    ∃ j : ℕ, heightScale N θ j / θ < t ∧ t ≤ heightScale N θ j := by
  have hθ0 : 0 < θ := by linarith
  obtain ⟨j, hj, hj'⟩ := exists_nat_pow_near
    ((one_le_div ht).mpr htN) hθ
  refine ⟨j, ?_, ?_⟩
  · rw [← heightScale_succ, heightScale]
    apply (div_lt_iff₀ (pow_pos hθ0 _)).mpr
    have := (div_lt_iff₀ ht).mp hj'
    nlinarith
  · apply (le_div_iff₀ (pow_pos hθ0 j)).mpr
    have := (le_div_iff₀ ht).mp hj
    nlinarith

/-- Adjacent bands cannot both contain the same logarithmic height. -/
theorem heightScale_unique {N i j : ℕ} {θ t : ℝ} (hθ : 1 < θ)
    (hi : heightScale N θ i / θ < t ∧ t ≤ heightScale N θ i)
    (hj : heightScale N θ j / θ < t ∧ t ≤ heightScale N θ j) : i = j := by
  have hanti := heightScale_antitone N hθ
  rcases lt_trichotomy i j with hij | hij | hij
  · have hle := hanti (Nat.succ_le_of_lt hij)
    rw [heightScale_succ] at hle
    linarith [hi.1, hj.2]
  · exact hij
  · have hle := hanti (Nat.succ_le_of_lt hij)
    rw [heightScale_succ] at hle
    linarith [hj.1, hi.2]

/-- A positive cutoff gives a finite range of possible indices, with no
maximum of an empty active set. -/
theorem heightScale_finite_cutoff (N : ℕ) {θ c : ℝ} (hθ : 1 < θ) (hc : 0 < c) :
    ∃ K : ℕ, ∀ j : ℕ, c ≤ heightScale N θ j → j < K := by
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt ((N : ℝ) / c) hθ
  refine ⟨K, ?_⟩
  intro j hj
  by_contra h
  have hpow := hK.trans_le (pow_le_pow_right₀ hθ.le (Nat.le_of_not_gt h))
  have hN := (div_lt_iff₀ hc).mp hpow
  have hcj := (le_div_iff₀ (pow_pos (by linarith : 0 < θ) j)).mp hj
  linarith

/-- The exact partition of (0,N], including uniqueness and containment. -/
theorem heightScale_partition {N : ℕ} {θ : ℝ} (hN : 0 < N) (hθ : 1 < θ) (t : ℝ) :
    (∃! j : ℕ, heightScale N θ j / θ < t ∧ t ≤ heightScale N θ j) ↔
      0 < t ∧ t ≤ (N : ℝ) := by
  constructor
  · rintro ⟨j, hj, _⟩
    have hp := heightScale_pos hN (show 0 < θ by linarith) j
    have hm := heightScale_antitone N hθ (Nat.zero_le j)
    rw [heightScale_zero] at hm
    exact ⟨(div_pos hp (by linarith)).trans hj.1, hj.2.trans hm⟩
  · rintro ⟨ht, htN⟩
    obtain ⟨j, hj⟩ := heightScale_cover hN hθ ht htN
    exact ⟨j, hj, fun k hk => heightScale_unique hθ hk hj⟩

/-- Each exact upper endpoint belongs to its own band. -/
theorem heightScale_endpoint {N : ℕ} {θ : ℝ} (hN : 0 < N) (hθ : 1 < θ) (j : ℕ) :
    heightScale N θ j / θ < heightScale N θ j ∧
      heightScale N θ j ≤ heightScale N θ j := by
  exact ⟨div_lt_self (heightScale_pos hN (by linarith) j) hθ, le_rfl⟩

end ErdosMahlerAudit.Gate10
