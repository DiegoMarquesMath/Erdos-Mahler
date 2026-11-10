module

public import ErdosMahlerAudit.Gate14.Arithmetic

/-! Absorption of the factor 3 for every real exponent strictly below τ. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate14
open Filter
open scoped Topology

variable {τ : ℝ} {t0 : ℕ} {f : List Bool → ℕ} {ξ : (ℕ → Bool) → ℝ} {K : Set ℝ}
  (hC : Gate13.CantorSpec τ t0 f ξ K)
include hC

theorem eventually_constant_absorbed (ε : ℕ → Bool) {s : ℝ} (hs : s < τ) :
    ∀ᶠ n : ℕ in atTop, 3 * (Q f ε n : ℝ) ^ (-τ) < (Q f ε n : ℝ) ^ (-s) := by
  have hg := ((tendsto_rpow_atTop (sub_pos.mpr hs)).comp
    (Q_real_tendsto hC ε)).eventually (eventually_gt_atTop (3 : ℝ))
  filter_upwards [hg] with n hn
  have hp : (0 : ℝ) < Q f ε n := by exact_mod_cast Q_pos ε n
  calc
    3 * (Q f ε n : ℝ) ^ (-τ) <
        (Q f ε n : ℝ) ^ (τ - s) * (Q f ε n : ℝ) ^ (-τ) :=
      mul_lt_mul_of_pos_right hn (Real.rpow_pos_of_pos hp _)
    _ = (Q f ε n : ℝ) ^ (-s) := by rw [← Real.rpow_add hp]; congr 1; ring

theorem eventually_approximation (ε : ℕ → Bool) {s : ℝ} (hs : s < τ) :
    ∀ᶠ n : ℕ in atTop,
      0 < ξ ε - (r f ε n : ℝ) ∧ ξ ε - (r f ε n : ℝ) < (Q f ε n : ℝ) ^ (-s) := by
  filter_upwards [eventually_constant_absorbed hC ε hs] with n hn
  exact ⟨displacement_pos hC ε n, (displacement hC ε n).2.trans hn⟩

theorem approximation_threshold (ε : ℕ → Bool) {s : ℝ} (hs : s < τ) :
    ∃ n0 : ℕ, ∀ n ≥ n0,
      0 < ξ ε - (r f ε n : ℝ) ∧ ξ ε - (r f ε n : ℝ) < (Q f ε n : ℝ) ^ (-s) :=
  eventually_atTop.mp (eventually_approximation hC ε hs)

end ErdosMahlerAudit.Gate14
