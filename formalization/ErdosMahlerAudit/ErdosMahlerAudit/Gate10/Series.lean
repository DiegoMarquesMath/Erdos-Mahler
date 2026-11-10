module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Data.Finset.Lattice.Fold

/-! The genuinely summable majorant in TeX 1051–1068. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate10
open Filter
open scoped Topology BigOperators

noncomputable def bandMajorant (θ : ℝ) (j : ℕ) : ℝ :=
  Real.exp (-((j : ℝ) * Real.log θ) / (52 * Real.log (2 + (j : ℝ) * Real.log θ)))

theorem bandMajorant_pos (θ : ℝ) (j : ℕ) : 0 < bandMajorant θ j := Real.exp_pos _

/-- A direct p-series comparison, with a constant depending only on fixed θ.
The analytic input is log²(y)=o(y), applied at y=2+j log θ. -/
theorem bandMajorant_eventually_le {θ : ℝ} (hθ : 1 < θ) :
    ∀ᶠ j : ℕ in atTop, bandMajorant θ j ≤
      (Real.log θ)⁻¹ ^ 2 * (1 / (j : ℝ) ^ 2) := by
  let h := Real.log θ
  have hh : 0 < h := Real.log_pos hθ
  have ht : Tendsto (fun j : ℕ => 2 + (j : ℝ) * h) atTop atTop :=
    tendsto_atTop_mono (fun j => by linarith :
      ∀ j : ℕ, (j : ℝ) * h ≤ 2 + (j : ℝ) * h)
      (tendsto_natCast_atTop_atTop.atTop_mul_const hh)
  have hb := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound
    (show (0 : ℝ) < 1 / 208 by norm_num)
  have hj : ∀ᶠ j : ℕ in atTop, 2 ≤ (j : ℝ) * h :=
    (tendsto_natCast_atTop_atTop.atTop_mul_const hh).eventually (eventually_ge_atTop 2)
  filter_upwards [ht.eventually hb, hj] with j hb hj
  have hy : 0 < 2 + (j : ℝ) * h := by linarith
  have hl : 0 < Real.log (2 + (j : ℝ) * h) := Real.log_pos (by linarith)
  dsimp only [id] at hb
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log (2 + (j : ℝ) * h))),
    Real.norm_eq_abs, abs_of_pos hy] at hb
  have hsq : 104 * Real.log (2 + (j : ℝ) * h) ^ 2 ≤ (j : ℝ) * h := by
    nlinarith
  have he : -((j : ℝ) * h) / (52 * Real.log (2 + (j : ℝ) * h)) ≤
      -(2 * Real.log (2 + (j : ℝ) * h)) := by
    apply (div_le_iff₀ (by positivity : 0 < 52 * Real.log (2 + (j : ℝ) * h))).mpr
    nlinarith
  have hjp : (0 : ℝ) < j := by nlinarith
  calc
    bandMajorant θ j ≤ Real.exp (-(2 * Real.log (2 + (j : ℝ) * h))) :=
      Real.exp_le_exp.mpr he
    _ = 1 / (2 + (j : ℝ) * h) ^ 2 := by
      rw [Real.exp_neg, show (2 : ℝ) * Real.log (2 + (j : ℝ) * h) =
        (2 : ℕ) * Real.log (2 + (j : ℝ) * h) by norm_num,
        Real.exp_nat_mul, Real.exp_log hy]
      simp only [one_div]
    _ ≤ 1 / ((j : ℝ) * h) ^ 2 := by
      apply one_div_le_one_div_of_le (sq_pos_of_pos (mul_pos hjp hh))
      nlinarith
    _ = _ := by dsimp [h]; field_simp

theorem bandMajorant_summable {θ : ℝ} (hθ : 1 < θ) : Summable (bandMajorant θ) := by
  have hp : Summable (fun j : ℕ => 1 / (j : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  apply (hp.mul_left ((Real.log θ)⁻¹ ^ 2)).of_norm_bounded_eventually_nat
  filter_upwards [bandMajorant_eventually_le hθ] with j hj
  simpa only [Real.norm_eq_abs, abs_of_pos (bandMajorant_pos θ j)] using hj

/-- Uniform control of every finite set of tail indices, including the empty set. -/
theorem bandMajorant_finite_tail {θ ε : ℝ} (hθ : 1 < θ) (hε : 0 < ε) :
    ∃ J : ℕ, ∀ s : Finset ℕ, (∀ j ∈ s, J ≤ j) →
      (∑ j ∈ s, bandMajorant θ j) < ε := by
  obtain ⟨s₀, hs₀⟩ := summable_iff_vanishing_norm.mp (bandMajorant_summable hθ) ε hε
  refine ⟨s₀.sup id + 1, ?_⟩
  intro s hs
  have hd : Disjoint s s₀ := Finset.disjoint_left.mpr (by
    intro j hj hj₀
    have hu : j ≤ s₀.sup id := Finset.le_sup (f := id) hj₀
    have hl := hs j hj
    omega)
  have hn : 0 ≤ ∑ j ∈ s, bandMajorant θ j :=
    Finset.sum_nonneg (fun j _ => (bandMajorant_pos θ j).le)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hn] using hs₀ s hd

end ErdosMahlerAudit.Gate10
