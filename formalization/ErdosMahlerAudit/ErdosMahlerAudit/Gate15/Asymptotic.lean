module

public import ErdosMahlerAudit.Gate15.Bands

/-! Uniformity over rationals for each fixed branch and each positive exponent gap. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate15
open Gate14 Filter
open scoped Topology

variable {τ : ℝ} {t0 : ℕ} {f : List Bool → ℕ} {ξ : (ℕ → Bool) → ℝ} {K : Set ℝ}

theorem index_tendsto (hA : ArithmeticLowerSpec τ t0 f ξ) (ε : ℕ → Bool) :
    Tendsto (t f ε) atTop atTop :=
  (strictMono_nat_of_lt_succ (hA.index_step ε)).tendsto_atTop

theorem nu_tendsto (hA : ArithmeticLowerSpec τ t0 f ξ) (ε : ℕ → Bool) :
    Tendsto (fun j => Gate02.nu (t f ε j)) atTop (𝓝 4) := by
  have hi : Tendsto (fun j => 1 / (t f ε j : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp (index_tendsto hA ε)
  simpa only [Gate02.nu, add_zero] using hi.const_add 4

theorem nu_eventually (hA : ArithmeticLowerSpec τ t0 f ξ) (hτ : 4 ≤ τ)
    (ε : ℕ → Bool) {δ : ℝ} (hδ : 0 < δ) :
    ∃ J : ℕ, ∀ j ≥ J, Gate02.nu (t f ε j) ≤ 4 + δ / 2 ∧
      Gate02.nu (t f ε j) ≤ τ + δ / 2 := by
  have he := (nu_tendsto hA ε).eventually (gt_mem_nhds (by linarith : (4 : ℝ) < 4 + δ / 2))
  apply eventually_atTop.mp
  filter_upwards [he] with j hj
  exact ⟨hj.le, by linarith⟩

theorem power_eventually {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℕ, ∀ v ≥ M, (32 : ℝ) ≤ (v : ℝ) ^ (δ / 2) := by
  exact eventually_atTop.mp (((tendsto_rpow_atTop (by linarith : 0 < δ / 2)).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 32))

theorem absorb_band_constant {v ν τ δ : ℝ} (hv : 1 ≤ v)
    (hν : ν ≤ τ + δ / 2) (hc : 32 ≤ v ^ (δ / 2)) :
    v ^ (-(τ + δ)) ≤ 1 / (32 * v ^ ν) := by
  have hp : 0 < v := by linarith
  have he := Real.rpow_le_rpow_of_exponent_le hv hν
  have hprod := mul_le_mul hc he (Real.rpow_nonneg hp.le _)
    (Real.rpow_nonneg hp.le _)
  have hid : v ^ (δ / 2) * v ^ (τ + δ / 2) = v ^ (τ + δ) := by
    rw [← Real.rpow_add hp]
    congr 1
    ring
  rw [hid] at hprod
  rw [Real.rpow_neg hp.le, ← one_div]
  exact one_div_le_one_div_of_le (by positivity) hprod

theorem high_denominator_in_interval (hC : Gate13.CantorSpec τ t0 f ξ K)
    (hA : ArithmeticLowerSpec τ t0 f ξ) (hτ : 4 ≤ τ)
    (ε : ℕ → Bool) {δ : ℝ} (hδ : 0 < δ) :
    ∃ V : ℕ, 3 ≤ V ∧ ∀ q : ℚ, 1 ≤ q → q ≤ 2 → V ≤ q.den →
      (q.den : ℝ) ^ (-(τ + δ)) ≤ |ξ ε - (q : ℝ)| := by
  obtain ⟨J, hJ⟩ := nu_eventually hA hτ ε hδ
  obtain ⟨M, hM⟩ := power_eventually hδ
  refine ⟨max (Q f ε J) M, (hA.denominator_three ε J).trans (le_max_left _ _), ?_⟩
  intro q hq1 hq2 hv
  have hJv := (le_max_left (Q f ε J) M).trans hv
  have hMv := (le_max_right (Q f ε J) M).trans hv
  have h0v := ((hA.denominator_strictMono ε).monotone (Nat.zero_le J)).trans hJv
  obtain ⟨j, hj, _⟩ := denominator_partition hA ε h0v
  have hjJ := band_index_ge hA ε hJv hj.2
  have hv1 : (1 : ℝ) ≤ q.den := by exact_mod_cast q.pos
  by_cases heq : q = r f ε j
  · exact (Real.rpow_le_rpow_of_exponent_le hv1 (by linarith : -(τ + δ) ≤ -τ)).trans
      (prescribed_case hA ε j heq).2.le
  · exact (absorb_band_constant hv1 (hJ j hjJ).2 (hM q.den hMv)).trans
      (nonprescribed_band hC hA hτ ε j q hq1 hq2 hj heq)

theorem outside_margin {x : ℝ} (hx1 : 1 < x) (hx2 : x < 2)
    (q : ℚ) (hq : ¬ (1 ≤ q ∧ q ≤ 2)) :
    0 < min (x - 1) (2 - x) ∧ min (x - 1) (2 - x) ≤ |x - (q : ℝ)| := by
  refine ⟨lt_min (by linarith) (by linarith), ?_⟩
  have hlo := min_le_left (x - 1) (2 - x)
  have hhi := min_le_right (x - 1) (2 - x)
  by_cases hq1 : 1 ≤ q
  · have hq2 : 2 < q := lt_of_not_ge (fun h => hq ⟨hq1, h⟩)
    have hr : (2 : ℝ) < (q : ℝ) := by exact_mod_cast hq2
    have ha := neg_le_abs (x - (q : ℝ))
    linarith
  · have hr : (q : ℝ) < 1 := by exact_mod_cast lt_of_not_ge hq1
    have ha := le_abs_self (x - (q : ℝ))
    linarith

theorem all_rational_high_denominator (hC : Gate13.CantorSpec τ t0 f ξ K)
    (hA : ArithmeticLowerSpec τ t0 f ξ) (hτ : 4 ≤ τ)
    (ε : ℕ → Bool) {δ : ℝ} (hδ : 0 < δ) :
    ∃ V : ℕ, ∀ q : ℚ, V ≤ q.den →
      (q.den : ℝ) ^ (-(τ + δ)) ≤ |ξ ε - (q : ℝ)| := by
  have hx : ξ ε ∈ Set.Ioo (1 : ℝ) 2 := hC.subset (by rw [hC.range_eq]; exact ⟨ε, rfl⟩)
  have hρ : 0 < min (ξ ε - 1) (2 - ξ ε) := lt_min (by linarith [hx.1]) (by linarith [hx.2])
  have he : ∀ᶠ v : ℕ in atTop,
      (v : ℝ) ^ (-(τ + δ)) < min (ξ ε - 1) (2 - ξ ε) :=
    ((tendsto_rpow_neg_atTop (by linarith : 0 < τ + δ)).comp
      tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds hρ)
  obtain ⟨M, hM⟩ := eventually_atTop.mp he
  obtain ⟨V, _, hV⟩ := high_denominator_in_interval hC hA hτ ε hδ
  refine ⟨max M V, ?_⟩
  intro q hv
  by_cases hq : 1 ≤ q ∧ q ≤ 2
  · exact hV q hq.1 hq.2 ((le_max_right _ _).trans hv)
  · exact (hM q.den ((le_max_left _ _).trans hv)).le.trans
      (outside_margin hx.1 hx.2 q hq).2

end ErdosMahlerAudit.Gate15
