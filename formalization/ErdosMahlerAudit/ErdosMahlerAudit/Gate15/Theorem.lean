module

public import ErdosMahlerAudit.Gate15.FiniteApproximants

/-! The same Gate 14 Cantor object, with uniform rational bounds and finite exceptions. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate15

/-- Exact upper approximation interface; no numeric supremum semantics is asserted. -/
structure UpperSpec (τ : ℝ) (t0 : ℕ) (f : List Bool → ℕ)
    (ξ : (ℕ → Bool) → ℝ) : Prop where
  high_denominator : ∀ ε : ℕ → Bool, ∀ δ : ℝ, 0 < δ →
    ∃ V : ℕ, ∀ q : ℚ, V ≤ q.den →
      (q.den : ℝ) ^ (-(τ + δ)) ≤ |ξ ε - (q : ℝ)|
  finite_too_good : ∀ ε : ℕ → Bool, ∀ s : ℝ, τ < s →
    {q : ℚ | 0 < |ξ ε - (q : ℝ)| ∧
      |ξ ε - (q : ℝ)| < (q.den : ℝ) ^ (-s)}.Finite

theorem upper_from_arithmetic {τ : ℝ} {t0 : ℕ} {f : List Bool → ℕ}
    {ξ : (ℕ → Bool) → ℝ} {K : Set ℝ}
    (hC : Gate13.CantorSpec τ t0 f ξ K)
    (hA : Gate14.ArithmeticLowerSpec τ t0 f ξ) (hτ : 4 ≤ τ) :
    UpperSpec τ t0 f ξ where
  high_denominator := fun ε _ hδ => all_rational_high_denominator hC hA hτ ε hδ
  finite_too_good := fun ε _ hs => finite_of_high_denominator hτ
    (fun _ hδ => all_rational_high_denominator hC hA hτ ε hδ) hs

/-- The two external number-theory propositions are ordinary, undischarged inputs.
One application of Gate 14 supplies all four existential witnesses. -/
theorem upper_irrationality_exponent
    (hST : Gate05.SubspaceTwoThreePrimitive) (hMatveev : Gate08.MatveevRationalThree)
    (τ : ℝ) (hτ : 4 ≤ τ) :
    ∃ (K : Set ℝ) (ξ : (ℕ → Bool) → ℝ) (t0 : ℕ) (f : List Bool → ℕ),
      Gate13.CantorSpec τ t0 f ξ K ∧ Gate14.ArithmeticLowerSpec τ t0 f ξ ∧
        UpperSpec τ t0 f ξ := by
  obtain ⟨K, ξ, t0, f, hC, hA⟩ := Gate14.prescribed_convergents_lower_exponent hST hMatveev τ hτ
  exact ⟨K, ξ, t0, f, hC, hA, upper_from_arithmetic hC hA hτ⟩

end ErdosMahlerAudit.Gate15
