module

public import ErdosMahlerAudit.Gate15.Asymptotic

/-! Finiteness of canonical rationals, including signed numerators. TeX 458–468. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate15

/-- Proved directly by the injective canonical numerator/denominator map. -/
theorem finite_bounded_denominator_near (x : ℝ) (V : ℕ) :
    {q : ℚ | q.den < V ∧ |x - (q : ℝ)| < 1}.Finite := by
  let B : ℤ := ⌈(|x| + 1) * (V : ℝ)⌉
  let F : ℚ → ℤ × ℕ := fun q => (q.num, q.den)
  have hinj : Function.Injective F := by
    intro p q hpq
    have hnum := congrArg Prod.fst hpq
    have hden := congrArg Prod.snd hpq
    dsimp [F] at hnum hden
    rw [← Rat.num_div_den p, ← Rat.num_div_den q, hnum, hden]
  have hs : F '' {q : ℚ | q.den < V ∧ |x - (q : ℝ)| < 1} ⊆
      Set.Icc (-B) B ×ˢ Set.Iio V := by
    rintro z ⟨q, hq, rfl⟩
    have hd : (0 : ℝ) < q.den := by exact_mod_cast q.pos
    have hdV : (q.den : ℝ) ≤ V := by exact_mod_cast hq.1.le
    have habs : |(q : ℝ)| ≤ |x| + 1 := by
      have ht := abs_sub_le (q : ℝ) x 0
      rw [sub_zero, sub_zero, abs_sub_comm (q : ℝ) x] at ht
      linarith [hq.2]
    have he : |(q.num : ℝ)| = |(q : ℝ)| * (q.den : ℝ) := by
      rw [Rat.cast_def, abs_div, abs_of_pos hd]
      field_simp
    have hbound : |(q.num : ℝ)| ≤ (B : ℝ) := by
      rw [he]
      exact (mul_le_mul habs hdV hd.le (by positivity)).trans (Int.le_ceil _)
    have hl : -B ≤ q.num := by exact_mod_cast (abs_le.mp hbound).1
    have hu : q.num ≤ B := by exact_mod_cast (abs_le.mp hbound).2
    exact ⟨⟨hl, hu⟩, hq.1⟩
  exact (((Set.finite_Icc (-B) B).prod (Set.finite_Iio V)).subset hs).of_finite_image hinj.injOn

theorem finite_of_high_denominator {x τ : ℝ} (hτ : 4 ≤ τ)
    (hhigh : ∀ δ : ℝ, 0 < δ → ∃ V : ℕ, ∀ q : ℚ, V ≤ q.den →
      (q.den : ℝ) ^ (-(τ + δ)) ≤ |x - (q : ℝ)|)
    {s : ℝ} (hs : τ < s) :
    {q : ℚ | 0 < |x - (q : ℝ)| ∧ |x - (q : ℝ)| < (q.den : ℝ) ^ (-s)}.Finite := by
  obtain ⟨V, hV⟩ := hhigh ((s - τ) / 2) (by linarith)
  apply (finite_bounded_denominator_near x V).subset
  intro q hq
  have hd : (1 : ℝ) ≤ q.den := by exact_mod_cast q.pos
  have he := Real.rpow_le_rpow_of_exponent_le hd
    (show -s ≤ -(τ + (s - τ) / 2) by linarith)
  have hden : q.den < V := by
    by_contra h
    exact (not_lt_of_ge (hV q (le_of_not_gt h))) (hq.2.trans_le he)
  have hone : (q.den : ℝ) ^ (-s) ≤ 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hd (show -s ≤ 0 by linarith)
  exact ⟨hden, hq.2.trans_le hone⟩

end ErdosMahlerAudit.Gate15
