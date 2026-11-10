module

public import ErdosMahlerAudit.Gate03.Denominators

/-! Convergent approximation for the actual reduced rational. We only need
the reduced denominator to be at most the integer continuant denominator;
we do not assume equality of these two representations. -/

public section
namespace ErdosMahlerAudit.Gate03

/-- Irrationality prevents termination at every continued-fraction index. -/
theorem alpha_not_terminated (n : ℕ) : ¬(GenContFract.of alpha).TerminatedAt n := by
  intro h
  have he := GenContFract.of_correctness_of_terminatedAt h
  rw [Real.convs_eq_convergent] at he
  exact alpha_irrational.ne_rat _ he

/-- Both continuants are integers, proved from the actual recurrence. -/
theorem continuants_integral (x : ℝ) (n : ℕ) :
    ∃ a b : ℤ, ((GenContFract.of x).contsAux n).a = a ∧
      ((GenContFract.of x).contsAux n).b = b := by
  induction n using Nat.twoStepInduction with
  | zero => exact ⟨1, 0, by simp [GenContFract.contsAux]⟩
  | one => exact ⟨⌊x⌋, 1, by simp [GenContFract.contsAux, GenContFract.of_h_eq_floor]⟩
  | more n ih ih' =>
    cases hs : (GenContFract.of x).s.get? n with
    | none => simpa only [GenContFract.contsAux, hs] using ih'
    | some gp =>
      obtain ⟨a, b, ha, hb⟩ := ih
      obtain ⟨c, d, hc, hd⟩ := ih'
      obtain ⟨hpa, z, hz⟩ := GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq hs
      refine ⟨z*c+a, z*d+b, ?_⟩
      rw [GenContFract.contsAux_recurrence hs rfl rfl]
      simp [hpa, hz, ha, hb, hc, hd]

/-- Positivity of the unreduced continuant denominator, derived from Fibonacci growth. -/
theorem continuant_den_pos (n : ℕ) : 0 < (GenContFract.of alpha).dens n := by
  have h := GenContFract.succ_nth_fib_le_of_nth_den
    (v := alpha) (n := n) (Or.inr (alpha_not_terminated (n-1)))
  have hf : (0 : ℝ) < Nat.fib (n+1) := by exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos n)
  exact hf.trans_le h

/-- Reduction cannot increase the positive integer denominator. -/
theorem convergent_den_le_continuant (n : ℕ) :
    ((Real.convergent alpha n).den : ℝ) ≤ (GenContFract.of alpha).dens n := by
  obtain ⟨a, b, ha, hb⟩ := continuants_integral alpha (n+1)
  have hnum : (GenContFract.of alpha).nums n = (a : ℝ) := ha
  have hden : (GenContFract.of alpha).dens n = (b : ℝ) := hb
  have hbpos : 0 < b := by exact_mod_cast (hden ▸ continuant_den_pos n)
  have hq : Real.convergent alpha n = Rat.divInt a b := by
    apply Rat.cast_injective (α := ℝ)
    rw [← Real.convs_eq_convergent, GenContFract.conv_eq_num_div_den, hnum, hden,
      Rat.cast_divInt]
  rw [hden, hq]
  exact_mod_cast Int.le_of_dvd hbpos (Rat.den_dvd a b)

/-- The non-strict estimate is enough for the translated-grid perturbation. -/
theorem convergent_error_le (n : ℕ) :
    |alpha - (Real.convergent alpha n : ℝ)| ≤
      1 / ((Real.convergent alpha n).den : ℝ)^2 := by
  have hq : (0 : ℝ) < (Real.convergent alpha n).den := by exact_mod_cast Rat.pos _
  have hden := convergent_den_le_continuant n
  have hmono := GenContFract.of_den_mono (v := alpha) (n := n)
  have herr := GenContFract.abs_sub_convs_le (alpha_not_terminated n)
  rw [Real.convs_eq_convergent] at herr
  apply herr.trans
  apply one_div_le_one_div_of_le (sq_pos_of_pos hq)
  nlinarith [continuant_den_pos n]

/-- Strictness follows since equality would make alpha rational. -/
theorem convergent_error_lt (n : ℕ) :
    |alpha - (Real.convergent alpha n : ℝ)| <
      1 / ((Real.convergent alpha n).den : ℝ)^2 := by
  apply lt_of_le_of_ne (convergent_error_le n)
  intro he
  rcases le_total 0 (alpha - (Real.convergent alpha n : ℝ)) with h | h
  · rw [abs_of_nonneg h] at he
    apply alpha_irrational.ne_rat
      (Real.convergent alpha n + 1 / ((Real.convergent alpha n).den : ℚ)^2)
    push_cast
    linarith
  · rw [abs_of_nonpos h] at he
    apply alpha_irrational.ne_rat
      (Real.convergent alpha n - 1 / ((Real.convergent alpha n).den : ℚ)^2)
    push_cast
    linarith

/-- Each member has an actual coprime convergent numerator and the paper's error bound. -/
theorem convergentDenominators_approximation {N : ℕ} (hN : N ∈ convergentDenominators) :
    0 < N ∧ ∃ p : ℤ, Nat.Coprime p.natAbs N ∧
      |alpha - (p : ℝ) / N| < 1 / (N : ℝ)^2 := by
  obtain ⟨n, rfl⟩ := hN
  refine ⟨Rat.pos _, (Real.convergent alpha n).num, Rat.reduced _, ?_⟩
  simpa only [Rat.cast_def] using convergent_error_lt n

/-- The translation is N*alpha, and i=0 and N=1 require no exception. -/
theorem translated_grid_error {N : ℕ} (hN : N ∈ convergentDenominators) :
    ∃ p : ℤ, Nat.Coprime p.natAbs N ∧ ∀ i : ℕ, i < N →
      |((N+i : ℕ) : ℝ)*alpha - ((N : ℝ)*alpha + (i : ℝ)*p/N)| < 1/(N : ℝ) := by
  obtain ⟨hpos, p, hcop, herr⟩ := convergentDenominators_approximation hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hpos
  refine ⟨p, hcop, ?_⟩
  intro i hi
  have hir : (i : ℝ) < N := by exact_mod_cast hi
  calc
    _ = (i : ℝ) * |alpha - (p : ℝ)/N| := by
      rw [Nat.cast_add]
      rw [show ((N : ℝ)+i)*alpha - ((N : ℝ)*alpha + (i : ℝ)*p/N) =
        (i : ℝ)*(alpha-(p : ℝ)/N) by ring, abs_mul, abs_of_nonneg (Nat.cast_nonneg i)]
    _ ≤ (i : ℝ) * (1/(N : ℝ)^2) := mul_le_mul_of_nonneg_left herr.le (Nat.cast_nonneg i)
    _ < (N : ℝ) * (1/(N : ℝ)^2) := mul_lt_mul_of_pos_right hir (by positivity)
    _ = 1/(N : ℝ) := by field_simp

end ErdosMahlerAudit.Gate03
