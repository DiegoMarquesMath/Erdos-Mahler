module

public import ErdosMahlerAudit.Gate16.Exponent

/-! Integration on the single inherited Cantor image, conditional on two external inputs. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate16

theorem approxOrder_of_infinite_good {τ : ℝ} {t0 : ℕ} {f : List Bool → ℕ}
    {ξ : (ℕ → Bool) → ℝ} (hA : Gate14.ArithmeticLowerSpec τ t0 f ξ)
    (ε : ℕ → Bool) {s : ℝ} (hs : 0 < s) (hsτ : s < τ) :
    ApproxOrder (ξ ε) s := by
  apply Set.Infinite.mono (s := {q : ℚ | q ∈ Set.range (Gate14.r f ε) ∧
    (∃ m : ℕ, q = Real.convergent (ξ ε) m) ∧
    (∃ A B : ℕ, q.num = (2 : ℤ) ^ A ∧ q.den = 3 ^ B) ∧
    0 < ξ ε - (q : ℝ) ∧ ξ ε - (q : ℝ) < (q.den : ℝ) ^ (-s)})
  · intro q hq
    have he := hq.2.2.2
    change 0 < |ξ ε - (q : ℝ)| ∧ |ξ ε - (q : ℝ)| < (q.den : ℝ) ^ (-s)
    simpa only [abs_of_pos he.1] using he
  · exact hA.infinite_good ε s hs hsτ

theorem branch_exponent {τ : ℝ} {t0 : ℕ} {f : List Bool → ℕ}
    {ξ : (ℕ → Bool) → ℝ} (hA : Gate14.ArithmeticLowerSpec τ t0 f ξ)
    (hU : Gate15.UpperSpec τ t0 f ξ) (hτ : 4 ≤ τ) (ε : ℕ → Bool) :
    irrationalityExponent (ξ ε) = ENNReal.ofReal τ := by
  have hpos : 0 < τ := by linarith
  apply le_antisymm
  · exact exponent_le_of_finite hpos (fun s hs => hU.finite_too_good ε s hs)
  · exact ofReal_le_exponent_of_infinite hpos
      (fun _ hs hsτ => approxOrder_of_infinite_good hA ε hs hsτ)

theorem infinite_prescribed_convergents {τ : ℝ} {t0 : ℕ} {f : List Bool → ℕ}
    {ξ : (ℕ → Bool) → ℝ} (hA : Gate14.ArithmeticLowerSpec τ t0 f ξ)
    (hτ : 4 ≤ τ) (ε : ℕ → Bool) :
    {q : ℚ | (∃ m : ℕ, q = Real.convergent (ξ ε) m) ∧
      (∃ A B : ℕ, q.num = (2 : ℤ)^A ∧ q.den = 3^B)}.Infinite := by
  have hi := hA.infinite_good ε 2 (by norm_num) (by linarith)
  refine Set.Infinite.mono ?_ hi
  intro q hq
  exact ⟨hq.2.1, hq.2.2.1⟩

/-- The sole Cantor selection is the one returned by Gate 15. The external
contracts are ordinary explicit hypotheses, not proved external theorems. -/
theorem erdos_mahler_main
    (hST : Gate05.SubspaceTwoThreePrimitive) (hMatveev : Gate08.MatveevRationalThree)
    (τ : ℝ) (hτ : 4 ≤ τ) :
    ∃ (K : Set ℝ) (ξ : (ℕ → Bool) → ℝ) (t0 : ℕ) (f : List Bool → ℕ),
      Gate13.CantorSpec τ t0 f ξ K ∧
      Gate14.ArithmeticLowerSpec τ t0 f ξ ∧
      Gate15.UpperSpec τ t0 f ξ ∧
      (∀ x ∈ K, Irrational x ∧
        irrationalityExponent x = ENNReal.ofReal τ ∧
        {q : ℚ | (∃ m : ℕ, q = Real.convergent x m) ∧
          (∃ A B : ℕ, q.num = (2 : ℤ)^A ∧ q.den = 3 ^ B)}.Infinite) := by
  obtain ⟨K, ξ, t0, f, hC, hA, hU⟩ :=
    Gate15.upper_irrationality_exponent hST hMatveev τ hτ
  refine ⟨K, ξ, t0, f, hC, hA, hU, ?_⟩
  intro x hx
  rw [hC.range_eq] at hx
  obtain ⟨ε, rfl⟩ := hx
  exact ⟨hA.irrational ε, branch_exponent hA hU hτ ε,
    infinite_prescribed_convergents hA hτ ε⟩

end ErdosMahlerAudit.Gate16
