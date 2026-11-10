module

public import ErdosMahlerAudit.Gate14.LowerExponent

/-! Irrationality from the actual rational-separation lemma, not an assumption. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate14
open Filter

variable {τ : ℝ} {t0 : ℕ} {f : List Bool → ℕ} {ξ : (ℕ → Bool) → ℝ} {K : Set ℝ}
  (hC : Gate13.CantorSpec τ t0 f ξ K)
include hC

theorem branch_irrational (hτ : 4 ≤ τ) (ε : ℕ → Bool) : Irrational (ξ ε) := by
  rintro ⟨u, hu⟩
  have hg := (Q_real_tendsto hC ε).eventually (eventually_gt_atTop (u.den : ℝ))
  obtain ⟨n, hn, hlarge⟩ := ((eventually_approximation hC ε
    (show (2 : ℝ) < τ by linarith)).and hg).exists
  have hne : u ≠ r f ε n := by
    intro he
    rw [← he, hu, sub_self] at hn
    exact (lt_irrefl 0) hn.1
  have hsep := rational_separation hne
  rw [r_den, hu, abs_of_pos hn.1] at hsep
  have hp : (0 : ℝ) < Q f ε n := by exact_mod_cast Q_pos ε n
  have huPos : (0 : ℝ) < u.den := by exact_mod_cast u.pos
  have hsmall : ξ ε - (r f ε n : ℝ) < 1 / (Q f ε n : ℝ) ^ 2 := by
    simpa only [Real.rpow_neg (le_of_lt hp), Real.rpow_ofNat, one_div] using hn.2
  have hreverse : 1 / (Q f ε n : ℝ) ^ 2 < 1 / ((u.den : ℝ) * Q f ε n) := by
    apply one_div_lt_one_div_of_lt (mul_pos huPos hp)
    nlinarith
  exact (not_lt_of_ge hsep) (hsmall.trans hreverse)

end ErdosMahlerAudit.Gate14
