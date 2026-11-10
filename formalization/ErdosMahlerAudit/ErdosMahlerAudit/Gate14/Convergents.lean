module

public import ErdosMahlerAudit.Gate14.Irrationality

/-! Legendre for the actual real branch limit and the actual reduced rational. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate14

/-- Strict even at q = 3 and τ = 4. -/
theorem legendre_constant {q τ : ℝ} (hq : 3 ≤ q) (hτ : 4 ≤ τ) :
    3 * q ^ (-τ) < 1 / (2 * q ^ 2) := by
  have hp : 0 < q := by linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le (show 1 ≤ q by linarith) (neg_le_neg hτ)
  have hbound : q ^ (-τ) ≤ 1 / q ^ 4 := by
    simpa only [Real.rpow_neg hp.le, Real.rpow_ofNat, one_div] using hpow
  have hs : 6 < q ^ 2 := by nlinarith
  have hstrict : 3 / q ^ 4 < 1 / (2 * q ^ 2) := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_pos (sq_pos_of_pos hp) (sub_pos.mpr hs)]
  calc
    3 * q ^ (-τ) ≤ 3 / q ^ 4 := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 3)
    _ < 1 / (2 * q ^ 2) := hstrict

variable {τ : ℝ} {t0 : ℕ} {f : List Bool → ℕ} {ξ : (ℕ → Bool) → ℝ} {K : Set ℝ}
  (hC : Gate13.CantorSpec τ t0 f ξ K)
include hC

theorem legendre_chain (hτ : 4 ≤ τ) (ε : ℕ → Bool) (n : ℕ) :
    0 < |ξ ε - (r f ε n : ℝ)| ∧
    |ξ ε - (r f ε n : ℝ)| < 3 * (Q f ε n : ℝ) ^ (-τ) ∧
    3 * (Q f ε n : ℝ) ^ (-τ) < 1 / (2 * (Q f ε n : ℝ) ^ 2) := by
  rw [abs_of_pos (displacement_pos hC ε n)]
  exact ⟨displacement_pos hC ε n, (displacement hC ε n).2,
    legendre_constant (by exact_mod_cast Q_three_le hC ε n) hτ⟩

theorem regular_convergent (hτ : 4 ≤ τ) (ε : ℕ → Bool) (n : ℕ) :
    ∃ m : ℕ, r f ε n = Real.convergent (ξ ε) m := by
  apply Real.exists_rat_eq_convergent
  rw [r_den]
  exact (legendre_chain hC hτ ε n).2.1.trans (legendre_chain hC hτ ε n).2.2

/-- Explicit bridge to the standard floor/reciprocal regular-CF computation. -/
theorem regular_convs (hτ : 4 ≤ τ) (ε : ℕ → Bool) (n : ℕ) :
    ∃ m : ℕ, (GenContFract.of (ξ ε)).convs m = (r f ε n : ℝ) := by
  obtain ⟨m, hm⟩ := regular_convergent hC hτ ε n
  exact ⟨m, by rw [Real.convs_eq_convergent, ← hm]⟩

/-- Infinitely many genuine prescribed regular convergents at each smaller order. -/
theorem infinitely_many_good_convergents (hτ : 4 ≤ τ) (ε : ℕ → Bool)
    {s : ℝ} (hs : s < τ) :
    {q : ℚ | q ∈ Set.range (r f ε) ∧
      (∃ m : ℕ, q = Real.convergent (ξ ε) m) ∧
      (∃ A B : ℕ, q.num = (2 : ℤ) ^ A ∧ q.den = 3 ^ B) ∧
      0 < ξ ε - (q : ℝ) ∧ ξ ε - (q : ℝ) < (q.den : ℝ) ^ (-s)}.Infinite := by
  obtain ⟨n0, hn0⟩ := approximation_threshold hC ε hs
  have hinj : Function.Injective (fun n : ℕ => r f ε (n + n0)) := by
    intro m n h
    have := r_injective hC ε h
    omega
  apply (Set.infinite_range_of_injective hinj).mono
  rintro q ⟨n, rfl⟩
  have ha := hn0 (n + n0) (by omega)
  refine ⟨⟨n + n0, rfl⟩, regular_convergent hC hτ ε (n + n0),
    ⟨a (t f ε (n + n0)), t f ε (n + n0), r_num _ _, r_den _ _⟩, ha.1, ?_⟩
  simpa only [r_den] using ha.2

end ErdosMahlerAudit.Gate14
