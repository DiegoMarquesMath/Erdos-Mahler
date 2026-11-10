module

public import ErdosMahlerAudit.Gate08.Rigidity
public import Mathlib.Data.Int.Interval

/-! Counting the actual class fibers through injective distinct-fraction indices. -/

public section
namespace ErdosMahlerAudit.Gate08
open Gate06 Gate07

theorem selectedFiber_card_at_threshold (hMatveev : MatveevRationalThree)
    {N : ℕ} {ν θ w : ℝ} (hθ : 1 < θ) (hθν : θ < ν / 4) (hw : 1 ≤ w)
    (hx : rigidityThreshold hMatveev ≤ Real.log ((N : ℝ) / w))
    (c : PositiveRatAdd ⧸ multipleSubgroup PositiveRatAdd
      (leastPower (Real.log ((N : ℝ) / w)))) :
    ((selectedFiber N ν θ w (leastPower (Real.log ((N : ℝ) / w))) c).card : ℝ) ≤ 13 * w := by
  classical
  let q := leastPower (Real.log ((N : ℝ) / w))
  let F := selectedFiber N ν θ w q c
  change (F.card : ℝ) ≤ 13 * w
  by_cases hF : F.Nonempty
  · let toX : F → selectedFractions N ν θ w := fun z => ⟨positiveValue z.val, by
      rw [← selectedPositive_value_image N ν θ w]
      exact Finset.mem_image.mpr ⟨z.val, (Finset.mem_filter.mp z.property).1, rfl⟩⟩
    have htoX : Function.Injective toX := by
      intro z z' he
      apply Subtype.ext
      apply positiveValue_injective
      have hv : (toX z).val = (toX z').val := congrArg Subtype.val he
      exact hv
    obtain ⟨anchor, hanchor⟩ := hF
    let s := toX ⟨anchor, hanchor⟩
    let d : ℤ := ⌈5 * w⌉
    let J := Finset.Icc ((representative s : ℤ) - d) ((representative s : ℤ) + d)
    have hd : 5 * w ≤ (d : ℝ) := Int.le_ceil _
    have hd0 : 0 ≤ d := by
      have : (0 : ℝ) ≤ d := by linarith
      exact_mod_cast this
    have hgap (z : F) : |(representative (toX z) : ℝ) - (representative s : ℝ)| ≤ 5 * w := by
      have hc0 (u : F) : classMap q (selectedLift (toX u)) = c := by
        have hv : selectedLift (toX u) = u.val := by
          apply positiveValue_injective
          rfl
        rw [hv]
        exact (Finset.mem_filter.mp u.property).2
      have hclass := (hc0 z).trans (hc0 ⟨anchor, hanchor⟩).symm
      have hg := index_gap_at_threshold hMatveev hθ hθν hw hx s (toX z) hclass
      have hh := two_w_add_log_two_le hw
      have hl3 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3)
      norm_num at hl3
      have habs := abs_nonneg ((representative (toX z) : ℝ) - (representative s : ℝ))
      nlinarith [mul_nonneg habs (by linarith : 0 ≤ Real.log 3 - 2 / 3)]
    let f : F → J := fun z => ⟨(representative (toX z) : ℤ), by
      apply Finset.mem_Icc.mpr
      have hh := abs_le.mp ((hgap z).trans hd)
      constructor
      · have hr : (representative s : ℝ) - (d : ℝ) ≤ representative (toX z) := by
          linarith [hh.1]
        exact_mod_cast hr
      · have hr : (representative (toX z) : ℝ) ≤ (representative s : ℝ) + (d : ℝ) := by
          linarith [hh.2]
        exact_mod_cast hr⟩
    have hf : Function.Injective f := by
      intro z z' he
      apply htoX
      apply representative_injective N ν θ w
      have hi : (representative (toX z) : ℤ) = (representative (toX z') : ℤ) :=
        congrArg Subtype.val he
      exact_mod_cast hi
    have hcJ : F.card ≤ J.card := by
      simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf
    have hcard : (J.card : ℝ) = 2 * (d : ℝ) + 1 := by
      have hci := Int.card_Icc_of_le (a := (representative s : ℤ) - d)
        (b := (representative s : ℤ) + d) (by omega)
      have he : (J.card : ℤ) = 2 * d + 1 := by dsimp [J]; omega
      exact_mod_cast he
    have hceil : (d : ℝ) < 5 * w + 1 := Int.ceil_lt_add_one _
    have hcR : (F.card : ℝ) ≤ J.card := by exact_mod_cast hcJ
    rw [hcard] at hcR
    linarith
  · have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    rw [he, Finset.card_empty, Nat.cast_zero]
    linarith

/-- Actual Lemma 3.5 class-size conclusion. The visible absolute constant is 13;
the single external input is MatveevRationalThree. -/
theorem selected_class_card_le (hMatveev : MatveevRationalThree) :
    ∃ C x₀ : ℝ, C = 13 ∧ 0 < C ∧ 0 < x₀ ∧ ∀ (N : ℕ) (ν θ w : ℝ),
      N ∈ convergentDenominators → 4 < ν → ν ≤ 5 → 1 < θ → θ < ν / 4 → 1 ≤ w →
      x₀ ≤ Real.log ((N : ℝ) / w) →
      ∀ c ∈ selectedClasses N ν θ w (leastPower (Real.log ((N : ℝ) / w))),
      ((selectedFiber N ν θ w (leastPower (Real.log ((N : ℝ) / w))) c).card : ℝ) ≤ C * w := by
  refine ⟨13, rigidityThreshold hMatveev, rfl, by norm_num, rigidityThreshold_pos hMatveev, ?_⟩
  intro N ν θ w _hN _hν4 _hν5 hθ hθν hw hx c _hc
  exact selectedFiber_card_at_threshold hMatveev hθ hθν hw hx c

end ErdosMahlerAudit.Gate08
