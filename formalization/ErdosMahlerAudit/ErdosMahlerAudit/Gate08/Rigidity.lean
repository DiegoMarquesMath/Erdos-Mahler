module

public import ErdosMahlerAudit.Gate08.Weighted
public import ErdosMahlerAudit.Gate08.Valuation

/-! Applying the sole external input and forcing the actual ratio identity. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate08
open Gate06 Gate07

noncomputable def matveevConstant (hMatveev : MatveevRationalThree) : ℝ :=
  Classical.choose hMatveev

theorem matveevConstant_pos (hMatveev : MatveevRationalThree) :
    0 < matveevConstant hMatveev := (Classical.choose_spec hMatveev).1

theorem matveev_specialization (hMatveev : MatveevRationalThree)
    {N b c q : ℕ} {ν θ w : ℝ} {g : ℚ}
    (hb : b ∈ exceptionalBand N ν θ w) (hc : c ∈ exceptionalBand N ν θ w)
    (hq : 0 < q) (hw : 1 ≤ w) (hg : 0 < g) (hne : g ≠ 1)
    (he : selectedFraction N ν θ w c / selectedFraction N ν θ w b = g ^ q)
    (hz : linearForm b c q g ≠ 0) :
    -matveevConstant hMatveev * Real.log 2 * Real.log 3 * (3 * w / q) *
      (1 + Real.log (weightedSize b c q w)) < Real.log |linearForm b c q g| := by
  have hs : selectedFraction N ν θ w b ∈ selectedFractions N ν θ w :=
    Finset.mem_image.mpr ⟨b, hb, rfl⟩
  have ht : selectedFraction N ν θ w c ∈ selectedFractions N ν θ w :=
    Finset.mem_image.mpr ⟨c, hc, rfl⟩
  have hgH := selected_root_height hs ht hq hw hg hne he
  have h2 : (4 / 25 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this
    linarith
  have h3 : (4 / 25 : ℝ) ≤ Real.log 3 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at this
    linarith
  have ha3 : 3 * w / (q : ℝ) ≠ 0 := by
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
    positivity
  have h := (Classical.choose_spec hMatveev).2 (2 : ℚ) (3 : ℚ) g
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hg hne
    ((a c : ℤ) - (a b : ℤ)) (-((c : ℤ) - (b : ℤ))) (-(q : ℤ))
    (Real.log 2) (Real.log 3) (3 * w / q)
    (by norm_num [rationalHeight])
    (by simp only [Rat.cast_ofNat, abs_of_pos log_two_pos, le_refl]) h2
    (by norm_num [rationalHeight])
    (by simp only [Rat.cast_ofNat, abs_of_pos log_three_pos, le_refl]) h3
    hgH.2.1 hgH.2.2.1 hgH.2.2.2
  have hform : (((a c : ℤ) - (a b : ℤ) : ℤ) : ℝ) * Real.log (2 : ℚ) +
      ((-((c : ℤ) - (b : ℤ)) : ℤ) : ℝ) * Real.log (3 : ℚ) +
      ((-(q : ℤ) : ℤ) : ℝ) * Real.log (g : ℝ) = linearForm b c q g := by
    push_cast
    dsimp [linearForm]
    ring
  dsimp only at h
  rw [hform] at h
  have hbval : max 1
      (max (|(((a c : ℤ) - (a b : ℤ) : ℤ) : ℝ)| * Real.log (2 : ℝ) / (3 * w / q))
      (max (|((-((c : ℤ) - (b : ℤ)) : ℤ) : ℝ)| * Real.log (3 : ℝ) / (3 * w / q))
        (|((-(q : ℤ) : ℤ) : ℝ)| * (3 * w / q) / (3 * w / q)))) =
      weightedSize b c q w := by
    simp only [Int.cast_sub, Int.cast_natCast, Int.cast_neg, abs_neg,
      Nat.abs_cast, mul_div_cancel_right₀ _ ha3, weightedSize]
  norm_num only [Rat.cast_ofNat] at h
  rw [hbval] at h
  exact h hz

noncomputable def rigidityThreshold (hMatveev : MatveevRationalThree) : ℝ :=
  100 * (matveevConstant hMatveev + 1)

theorem rigidityThreshold_pos (hMatveev : MatveevRationalThree) :
    0 < rigidityThreshold hMatveev := by
  dsimp [rigidityThreshold]
  linarith [matveevConstant_pos hMatveev]

theorem selected_linearForm_zero (hMatveev : MatveevRationalThree)
    {N b c : ℕ} {ν θ w : ℝ} {g : ℚ}
    (hb : b ∈ exceptionalBand N ν θ w) (hc : c ∈ exceptionalBand N ν θ w)
    (hθ : 1 < θ) (hθν : θ < ν / 4) (hw : 1 ≤ w)
    (hx : rigidityThreshold hMatveev ≤ Real.log ((N : ℝ) / w))
    (hg : 0 < g) (hne : g ≠ 1)
    (he : selectedFraction N ν θ w c / selectedFraction N ν θ w b =
      g ^ leastPower (Real.log ((N : ℝ) / w))) :
    linearForm b c (leastPower (Real.log ((N : ℝ) / w))) g = 0 := by
  let x := Real.log ((N : ℝ) / w)
  let q := leastPower x
  let C := matveevConstant hMatveev
  have hC : 0 < C := matveevConstant_pos hMatveev
  have hxC : 100 * (C + 1) ≤ x := hx
  have hx2 : 2 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hw0 : 0 < w := by linarith
  have hq : 0 < q := leastPower_pos x
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hqbound : x ^ 2 ≤ (q : ℝ) := (leastPower_bounds hx2).1
  have hB := weightedSize_log_bound hb hc hw hx2
  change 1 + Real.log (weightedSize b c q w) ≤ 3 * x at hB
  by_contra hz
  have hlo := matveev_specialization hMatveev hb hc hq hw hg hne he hz
  change -C * Real.log 2 * Real.log 3 * (3 * w / q) *
    (1 + Real.log (weightedSize b c q w)) < Real.log |linearForm b c q g| at hlo
  have h2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have h3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have h23 : Real.log 2 * Real.log 3 ≤ 2 := by
    nlinarith [mul_le_mul h2 h3 log_three_pos.le (by norm_num : (0 : ℝ) ≤ 1)]
  have hA : 0 ≤ C * Real.log 2 * Real.log 3 * (3 * w / q) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hB hA
  have hfactor : 0 ≤ C * (3 * w / q) * (3 * x) := by positivity
  have hmul2 := mul_le_mul_of_nonneg_right h23 hfactor
  have hlow : -Real.log |linearForm b c q g| < 18 * C * w * x / q := by
    have halg : (Real.log 2 * Real.log 3) * (C * (3 * w / q) * (3 * x)) =
        C * Real.log 2 * Real.log 3 * (3 * w / q) * (3 * x) := by ring
    have halg2 : 2 * (C * (3 * w / q) * (3 * x)) = 18 * C * w * x / q := by ring
    rw [halg, halg2] at hmul2
    nlinarith [hmul, hmul2, hlo]
  have herr := selected_linearForm_small hb hc hg he
  have hΛpos : 0 < |linearForm b c q g| := abs_pos.mpr hz
  have hlog := Real.log_lt_log hΛpos herr
  rw [Real.log_mul (by norm_num : (1 / 8 : ℝ) ≠ 0) (Real.exp_ne_zero _),
    Real.log_exp] at hlog
  have hlog8 : Real.log (1 / 8 : ℝ) < 0 :=
    Real.log_neg (by norm_num) (by norm_num)
  have hνw : 4 * w < ν * w / θ := by
    apply (lt_div_iff₀ (by linarith : 0 < θ)).mpr
    nlinarith [mul_pos hw0 (by linarith : 0 < ν - 4 * θ)]
  have hupper : 4 * w < -Real.log |linearForm b c q g| := by
    simp only [neg_mul, neg_div] at hlog
    linarith
  have hbound : 4 * w < 18 * C * w * x / (q : ℝ) := hupper.trans hlow
  have hcross := (lt_div_iff₀ hq0).mp hbound
  have hcancel : 4 * (q : ℝ) < 18 * C * x := by
    nlinarith [hcross]
  have : 4 * x ^ 2 < 18 * C * x := lt_of_le_of_lt (by nlinarith [hqbound]) hcancel
  nlinarith [mul_nonneg hx0.le (by linarith : 0 ≤ 4 * x - 18 * C)]

/-- At a concrete absolute threshold, for the chosen distinct-fraction representatives. -/
theorem ratio_rigidity_at_threshold (hMatveev : MatveevRationalThree)
    {N : ℕ} {ν θ w : ℝ} (hθ : 1 < θ) (hθν : θ < ν / 4) (hw : 1 ≤ w)
    (hx : rigidityThreshold hMatveev ≤ Real.log ((N : ℝ) / w))
    (s t : selectedFractions N ν θ w)
    (hc : classMap (leastPower (Real.log ((N : ℝ) / w))) (selectedLift t) =
      classMap (leastPower (Real.log ((N : ℝ) / w))) (selectedLift s)) :
    t.val / s.val = R (representative t) / R (representative s) := by
  by_cases hst : s = t
  · subst t
    rw [div_self (selectedFractions_positive s.property).ne', div_self (R_pos _).ne']
  · obtain ⟨g, hg, hne, he⟩ := selected_root s t hst hc
    have hbs := representative_spec s
    have hct := representative_spec t
    have he' : selectedFraction N ν θ w (representative t) /
        selectedFraction N ν θ w (representative s) = g ^ leastPower (Real.log ((N : ℝ) / w)) := by
      simpa only [hbs.2, hct.2] using he
    exact ratio_eq_of_linearForm_zero (selectedFractions_positive s.property)
      (selectedFractions_positive t.property) hg he
      (selected_linearForm_zero hMatveev hbs.1 hct.1 hθ hθν hw hx hg hne he')

/-- Lemma 3.5 ratio conclusion, with a single absolute threshold. -/
theorem same_class_ratio_rigidity (hMatveev : MatveevRationalThree) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ ∀ (N : ℕ) (ν θ w : ℝ),
      N ∈ convergentDenominators → 4 < ν → ν ≤ 5 → 1 < θ → θ < ν / 4 → 1 ≤ w →
      x₀ ≤ Real.log ((N : ℝ) / w) → ∀ s t : selectedFractions N ν θ w,
      classMap (leastPower (Real.log ((N : ℝ) / w))) (selectedLift t) =
        classMap (leastPower (Real.log ((N : ℝ) / w))) (selectedLift s) →
      t.val / s.val = R (representative t) / R (representative s) := by
  refine ⟨rigidityThreshold hMatveev, rigidityThreshold_pos hMatveev, ?_⟩
  intro N ν θ w _hN _hν4 _hν5 hθ hθν hw hx s t hc
  exact ratio_rigidity_at_threshold hMatveev hθ hθν hw hx s t hc

theorem index_gap_at_threshold (hMatveev : MatveevRationalThree)
    {N : ℕ} {ν θ w : ℝ} (hθ : 1 < θ) (hθν : θ < ν / 4) (hw : 1 ≤ w)
    (hx : rigidityThreshold hMatveev ≤ Real.log ((N : ℝ) / w))
    (s t : selectedFractions N ν θ w)
    (hc : classMap (leastPower (Real.log ((N : ℝ) / w))) (selectedLift t) =
      classMap (leastPower (Real.log ((N : ℝ) / w))) (selectedLift s)) :
    |(representative t : ℝ) - (representative s : ℝ)| * Real.log 3 ≤ 2 * w + Real.log 2 :=
  index_gap_of_ratio_eq s.property t.property
    (ratio_rigidity_at_threshold hMatveev hθ hθν hw hx s t hc)

theorem same_class_index_gap (hMatveev : MatveevRationalThree) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ ∀ (N : ℕ) (ν θ w : ℝ),
      N ∈ convergentDenominators → 4 < ν → ν ≤ 5 → 1 < θ → θ < ν / 4 → 1 ≤ w →
      x₀ ≤ Real.log ((N : ℝ) / w) → ∀ s t : selectedFractions N ν θ w,
      classMap (leastPower (Real.log ((N : ℝ) / w))) (selectedLift t) =
        classMap (leastPower (Real.log ((N : ℝ) / w))) (selectedLift s) →
      |(representative t : ℝ) - (representative s : ℝ)| * Real.log 3 ≤ 2 * w + Real.log 2 := by
  refine ⟨rigidityThreshold hMatveev, rigidityThreshold_pos hMatveev, ?_⟩
  intro N ν θ w _hN _hν4 _hν5 hθ hθν hw hx s t hc
  exact index_gap_at_threshold hMatveev hθ hθν hw hx s t hc

end ErdosMahlerAudit.Gate08
