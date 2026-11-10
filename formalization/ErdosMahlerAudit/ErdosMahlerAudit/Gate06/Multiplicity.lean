module

public import ErdosMahlerAudit.Gate06.Band

/-! Absolute multiplicity from the arbitrary-witness rotation bound, TeX 691–703. -/

public section
namespace ErdosMahlerAudit.Gate06
open scoped BigOperators

/-- Strict cube-root cutoff, with no eventual lower bound on N. -/
theorem denominator_decay {N : ℕ} (hN : 0 < N) {ν v : ℝ}
    (hν : 4 < ν) (hv : (N : ℝ) ^ (1 / 3 : ℝ) < v) :
    (N : ℝ) * v ^ (-ν) < 1 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hroot1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) :=
    Real.one_le_rpow hN1 (by norm_num)
  have hv1 : 1 < v := hroot1.trans_lt hv
  have hv0 : 0 < v := by linarith
  have hc := Real.rpow_lt_rpow (by positivity : 0 ≤ (N : ℝ) ^ (1 / 3 : ℝ))
    hv (by norm_num : (0 : ℝ) < 3)
  rw [← Real.rpow_mul (Nat.cast_nonneg N)] at hc
  norm_num at hc
  have hpow := Real.rpow_le_rpow_of_exponent_le hv1.le (by linarith : (3 : ℝ) ≤ ν)
  have hlt : (N : ℝ) < v ^ ν := hc.trans_le (by simpa using hpow)
  rw [Real.rpow_neg hv0.le, ← div_eq_mul_inv]
  exact (div_lt_one (Real.rpow_pos_of_pos hv0 ν)).mpr hlt

theorem selected_fiber_card_le {N : ℕ} {ν θ w : ℝ}
    (hN : N ∈ convergentDenominators) (hν : 4 < ν)
    {s : ℚ} (hs : s ∈ selectedFractions N ν θ w) :
    ((exceptionalBand N ν θ w).filter (fun b => selectedFraction N ν θ w b = s)).card ≤ 4 := by
  classical
  obtain ⟨b, hb, hbs⟩ := Finset.mem_image.mp hs
  have hspec := selectedFraction_spec hb
  rw [hbs] at hspec
  have hdec := denominator_decay (Gate03.convergentDenominators_pos hN) hν
    ((le_max_right _ _).trans_lt hspec.2.1)
  have hsub : (exceptionalBand N ν θ w).filter (fun b => selectedFraction N ν θ w b = s) ⊆
      Gate04.witnessIndices N ν s := by
    intro c hc
    obtain ⟨hc, hcs⟩ := Finset.mem_filter.mp hc
    have he := (selectedFraction_spec hc).1
    rw [hcs] at he
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr
      ⟨(mem_exceptionalBand.mp hc).1, (mem_exceptionalBand.mp hc).2.1⟩, he⟩
  have hcard := Gate04.witnessIndices_card_le hN hspec.1.2.2.2.1 hspec.1.2.2.2.2.1 ν
  have hcard' : (((exceptionalBand N ν θ w).filter
      (fun b => selectedFraction N ν θ w b = s)).card : ℝ) ≤
      (Gate04.witnessIndices N ν s).card := by exact_mod_cast Finset.card_le_card hsub
  have hlt : (((exceptionalBand N ν θ w).filter
      (fun b => selectedFraction N ν θ w b = s)).card : ℝ) < 4 := by linarith
  exact le_of_lt (by exact_mod_cast hlt)

/-- Exact Gate 06 interface. Parameters not needed by multiplicity are retained
so that the domain is precisely the manuscript's shared domain. -/
theorem exceptional_band_multiplicity
    (N : ℕ) (ν θ w : ℝ) (hN : N ∈ convergentDenominators)
    (hν4 : 4 < ν) (_hν5 : ν ≤ 5) (_hθ1 : 1 < θ) (_hθν : θ < ν / 4) (_hw : 0 < w) :
    (exceptionalBand N ν θ w).card ≤ 4 * (selectedFractions N ν θ w).card := by
  classical
  rw [Finset.card_eq_sum_card_image (selectedFraction N ν θ w)]
  calc
    _ ≤ ∑ _s ∈ selectedFractions N ν θ w, 4 :=
      Finset.sum_le_sum (fun s hs => selected_fiber_card_le hN hν4 hs)
    _ = _ := by simp [mul_comm]

end ErdosMahlerAudit.Gate06
