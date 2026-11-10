module

public import ErdosMahlerAudit.RationalArithmetic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Algebra.ContinuedFractions.Computation.ApproximationCorollaries

/-! Actual reduced convergent denominators. No monotonicity or distinctness
of the initial denominators is needed: convergence and a lattice separation
argument prove the stronger eventual escape from every bounded height. -/

public section
namespace ErdosMahlerAudit.Gate03

/-- Irrational numbers have a positive distance from the integer lattice. -/
theorem irrational_integer_gap {x : ℝ} (hx : Irrational x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : ℤ, ε ≤ |x - z| := by
  let ε := min (x - (⌊x⌋ : ℝ)) ((⌊x⌋ : ℝ) + 1 - x)
  have hleft : 0 < x - (⌊x⌋ : ℝ) :=
    sub_pos.mpr (lt_of_le_of_ne (Int.floor_le x) (hx.ne_int _).symm)
  have hright : 0 < (⌊x⌋ : ℝ) + 1 - x := sub_pos.mpr (Int.lt_floor_add_one x)
  refine ⟨ε, lt_min hleft hright, ?_⟩
  intro z
  rcases le_or_gt z ⌊x⌋ with hz | hz
  · have hz' : (z : ℝ) ≤ (⌊x⌋ : ℝ) := by exact_mod_cast hz
    exact (min_le_left _ _).trans ((by linarith : x - (⌊x⌋ : ℝ) ≤ x - z).trans
      (le_abs_self _))
  · have hz' : (⌊x⌋ : ℝ) + 1 ≤ z := by exact_mod_cast hz
    exact (min_le_right _ _).trans ((by linarith : (⌊x⌋ : ℝ) + 1 - x ≤ -(x-z)).trans
      (neg_le_abs _))

/-- Bounded canonical denominators lie in the lattice with spacing 1/B!.
This is a separation lemma, not a replacement of the convergent set. -/
theorem irrational_bounded_denominator_gap {x : ℝ} (hx : Irrational x) (B : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q : ℚ, q.den ≤ B → ε ≤ |x - q| := by
  have hF : (0 : ℝ) < B.factorial := by exact_mod_cast Nat.factorial_pos B
  obtain ⟨δ, hδ, hgap⟩ := irrational_integer_gap
    (hx.mul_natCast (Nat.ne_of_gt (Nat.factorial_pos B)))
  refine ⟨δ / B.factorial, div_pos hδ hF, ?_⟩
  intro q hq
  obtain ⟨k, hk⟩ := Nat.dvd_factorial q.pos hq
  have heq : (q : ℝ) * B.factorial = ((q.num * (k : ℤ) : ℤ) : ℝ) := by
    rw [Rat.cast_def, hk, Nat.cast_mul]
    push_cast
    field_simp
  have h := hgap (q.num * (k : ℤ))
  rw [← heq, ← sub_mul, abs_mul, abs_of_pos hF] at h
  exact (div_le_iff₀ hF).mpr h

/-- The actual rational convergents tend to alpha, with their original index. -/
theorem convergent_alpha_epsilon (ε : ℝ) (hε : 0 < ε) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → |alpha - (Real.convergent alpha n : ℝ)| < ε := by
  simpa only [Real.convs_eq_convergent] using
    GenContFract.of_convergence_epsilon alpha ε hε

/-- Strong eventual claim; allows repeated initial denominators. -/
theorem convergent_denominators_eventually_gt (B : ℕ) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → B < (Real.convergent alpha n).den := by
  obtain ⟨ε, hε, hgap⟩ := irrational_bounded_denominator_gap alpha_irrational B
  obtain ⟨n0, hn0⟩ := convergent_alpha_epsilon ε hε
  refine ⟨n0, ?_⟩
  intro n hn
  by_contra h
  exact (not_lt_of_ge (hgap _ (le_of_not_gt h))) (hn0 n hn)

/-- Positivity belongs to every member of the unchanged range. -/
theorem convergentDenominators_pos {N : ℕ} (hN : N ∈ convergentDenominators) :
    0 < N := by
  obtain ⟨n, rfl⟩ := hN
  exact Rat.pos _

/-- Unboundedness of Gate 01's actual set, without external assumptions. -/
theorem convergentDenominators_unbounded :
    ∀ B : ℕ, ∃ N : ℕ, N ∈ convergentDenominators ∧ B ≤ N := by
  intro B
  obtain ⟨n0, hn0⟩ := convergent_denominators_eventually_gt B
  exact ⟨_, ⟨n0, rfl⟩, (hn0 n0 le_rfl).le⟩

/-- The range includes the initial denominator 1. -/
theorem one_mem_convergentDenominators : 1 ∈ convergentDenominators := by
  exact ⟨0, by simp⟩

end ErdosMahlerAudit.Gate03
