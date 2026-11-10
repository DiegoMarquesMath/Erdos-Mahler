module

public import ErdosMahlerAudit.Gate14.Convergents

/-! One inherited Cantor object, with all arithmetic conclusions for every branch. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate14
open Filter

/-- Transparent conclusions, all about the actual `t`, `Q`, `r` and inherited map `ξ`. -/
structure ArithmeticLowerSpec (τ : ℝ) (t0 : ℕ) (f : List Bool → ℕ)
    (ξ : (ℕ → Bool) → ℝ) : Prop where
  root : ∀ ε, t f ε 0 = t0
  height : ∀ ε n, t0 + n ≤ t f ε n
  index_pos : ∀ ε n, 0 < t f ε n
  index_step : ∀ ε n, t f ε n < t f ε (n + 1)
  denominator_pos : ∀ ε n, 0 < Q f ε n
  denominator_three : ∀ ε n, 3 ≤ Q f ε n
  denominator_step : ∀ ε n, Q f ε n < Q f ε (n + 1)
  denominator_triple : ∀ ε n, 3 * Q f ε n ≤ Q f ε (n + 1)
  denominator_strictMono : ∀ ε, StrictMono (Q f ε)
  denominator_tendsto : ∀ ε, Tendsto (Q f ε) atTop atTop
  denominator_real_tendsto : ∀ ε, Tendsto (fun n => (Q f ε n : ℝ)) atTop atTop
  numerator : ∀ ε n, (r f ε n).num = (2 : ℤ) ^ a (t f ε n)
  denominator : ∀ ε n, (r f ε n).den = Q f ε n
  reduced : ∀ ε n, Nat.Coprime (2 ^ a (t f ε n)) (Q f ε n)
  fraction : ∀ ε n, r f ε n = (2 : ℚ) ^ a (t f ε n) / (Q f ε n : ℚ)
  distinct : ∀ ε, Function.Injective (r f ε)
  infinite : ∀ ε, (Set.range (r f ε)).Infinite
  displacement : ∀ ε n, (Q f ε n : ℝ) ^ (-τ) < ξ ε - (r f ε n : ℝ) ∧
    ξ ε - (r f ε n : ℝ) < 3 * (Q f ε n : ℝ) ^ (-τ)
  irrational : ∀ ε, Irrational (ξ ε)
  legendre : ∀ ε n, 0 < |ξ ε - (r f ε n : ℝ)| ∧
    |ξ ε - (r f ε n : ℝ)| < 3 * (Q f ε n : ℝ) ^ (-τ) ∧
    3 * (Q f ε n : ℝ) ^ (-τ) < 1 / (2 * (Q f ε n : ℝ) ^ 2)
  convergent : ∀ ε n, ∃ m : ℕ, r f ε n = Real.convergent (ξ ε) m
  convs : ∀ ε n, ∃ m : ℕ, (GenContFract.of (ξ ε)).convs m = (r f ε n : ℝ)
  eventual : ∀ ε s, 0 < s → s < τ → ∃ n0 : ℕ, ∀ n ≥ n0,
    0 < ξ ε - (r f ε n : ℝ) ∧ ξ ε - (r f ε n : ℝ) < (Q f ε n : ℝ) ^ (-s)
  infinite_good : ∀ ε s, 0 < s → s < τ →
    {q : ℚ | q ∈ Set.range (r f ε) ∧
      (∃ m : ℕ, q = Real.convergent (ξ ε) m) ∧
      (∃ A B : ℕ, q.num = (2 : ℤ) ^ A ∧ q.den = 3 ^ B) ∧
      0 < ξ ε - (q : ℝ) ∧ ξ ε - (q : ℝ) < (q.den : ℝ) ^ (-s)}.Infinite

theorem arithmetic_from_cantor {τ : ℝ} {t0 : ℕ} {f : List Bool → ℕ}
    {ξ : (ℕ → Bool) → ℝ} {K : Set ℝ}
    (hC : Gate13.CantorSpec τ t0 f ξ K) (hτ : 4 ≤ τ) :
    ArithmeticLowerSpec τ t0 f ξ where
  root := t_zero hC
  height := t_height hC
  index_pos := t_pos hC
  index_step := t_step hC
  denominator_pos := Q_pos
  denominator_three := Q_three_le hC
  denominator_step := Q_step hC
  denominator_triple := Q_triple hC
  denominator_strictMono := Q_strictMono hC
  denominator_tendsto := Q_tendsto hC
  denominator_real_tendsto := Q_real_tendsto hC
  numerator := r_num
  denominator := r_den
  reduced := r_reduced
  fraction := r_eq
  distinct := r_injective hC
  infinite := r_range_infinite hC
  displacement := displacement hC
  irrational := branch_irrational hC hτ
  legendre := legendre_chain hC hτ
  convergent := regular_convergent hC hτ
  convs := regular_convs hC hτ
  eventual := fun ε _ _ hs => approximation_threshold hC ε hs
  infinite_good := fun ε _ _ hs => infinitely_many_good_convergents hC hτ ε hs

/-- Gate 14: the sole Cantor choice precedes all branch quantifiers.
The two external number-theory contracts remain ordinary explicit arguments. -/
theorem prescribed_convergents_lower_exponent
    (hST : Gate05.SubspaceTwoThreePrimitive) (hMatveev : Gate08.MatveevRationalThree)
    (τ : ℝ) (hτ : 4 ≤ τ) :
    ∃ (K : Set ℝ) (ξ : (ℕ → Bool) → ℝ) (t0 : ℕ) (f : List Bool → ℕ),
      Gate13.CantorSpec τ t0 f ξ K ∧ ArithmeticLowerSpec τ t0 f ξ := by
  obtain ⟨K, ξ, t0, f, hC⟩ := Gate13.cantor_set_of_tau hST hMatveev τ hτ
  exact ⟨K, ξ, t0, f, hC, arithmetic_from_cantor hC hτ⟩

end ErdosMahlerAudit.Gate14
