module

public import ErdosMahlerAudit.Gate08.Selection
public import Mathlib.NumberTheory.Height.NumberField

/-! Canonical rational logarithmic height, TeX 802–805 and 836–844. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate08

noncomputable def rationalHeight (z : ℚ) : ℝ :=
  Real.log (max z.num.natAbs z.den : ℕ)

theorem rationalHeight_eq_library (z : ℚ) : rationalHeight z = Height.logHeight₁ z :=
  (Rat.logHeight₁_eq_log_max z).symm

theorem rationalHeight_pow (z : ℚ) (q : ℕ) :
    rationalHeight (z ^ q) = (q : ℝ) * rationalHeight z := by
  simp only [rationalHeight_eq_library, Height.logHeight₁_pow]

theorem rationalHeight_inv (z : ℚ) : rationalHeight z⁻¹ = rationalHeight z := by
  simp only [rationalHeight_eq_library, Height.logHeight₁_inv]

theorem rationalHeight_mul (s t : ℚ) :
    rationalHeight (s * t) ≤ rationalHeight s + rationalHeight t := by
  simpa only [rationalHeight_eq_library] using Height.logHeight₁_mul_le s t

theorem rationalHeight_div (s t : ℚ) :
    rationalHeight (s / t) ≤ rationalHeight s + rationalHeight t := by
  simpa only [div_eq_mul_inv, rationalHeight_inv] using rationalHeight_mul s t⁻¹

theorem numerator_cast {z : ℚ} (hz : 0 ≤ z) :
    (z.num.natAbs : ℝ) = (z : ℝ) * (z.den : ℝ) := by
  have hn := Rat.num_nonneg.mpr hz
  have he : (z : ℝ) = (z.num : ℝ) / (z.den : ℝ) := by
    exact_mod_cast (Rat.num_div_den z).symm
  have hd : (z.den : ℝ) ≠ 0 := by exact_mod_cast z.den_ne_zero
  rw [he, div_mul_cancel₀ _ hd]
  calc
    _ = ((z.num.natAbs : ℤ) : ℝ) := by simp only [Int.cast_natCast]
    _ = _ := congrArg (fun n : ℤ => (n : ℝ)) (Int.natAbs_of_nonneg hn)

theorem log_two_le_height {z : ℚ} (hz : 0 < z) (hne : z ≠ 1) :
    Real.log 2 ≤ rationalHeight z := by
  have hn : 0 < z.num.natAbs := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hz.ne')
  have hm : 2 ≤ max z.num.natAbs z.den := by
    by_contra h
    have hnum : z.num.natAbs = 1 := by omega
    have hden : z.den = 1 := by have := z.pos; omega
    have hnum' : z.num = 1 := by
      have := Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hz.le)
      rw [hnum] at this
      exact this.symm
    apply hne
    rw [← Rat.num_div_den z, hnum', hden]
    norm_num
  exact Real.log_le_log (by norm_num) (by exact_mod_cast hm)

theorem abs_log_le_height {z : ℚ} (hz : 0 < z) :
    |Real.log (z : ℝ)| ≤ rationalHeight z := by
  have hn : 1 ≤ z.num.natAbs := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hz.ne')
  have hd : 1 ≤ z.den := z.pos
  have hn0 : (0 : ℝ) < z.num.natAbs := by exact_mod_cast hn
  have hd0 : (0 : ℝ) < z.den := by exact_mod_cast hd
  have hne : (z : ℝ) = (z.num.natAbs : ℝ) / z.den := by
    rw [numerator_cast hz.le, mul_div_cancel_right₀ _ hd0.ne']
  have hln : 0 ≤ Real.log (z.num.natAbs : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hld : 0 ≤ Real.log (z.den : ℝ) := Real.log_nonneg (by exact_mod_cast hd)
  have hln' : Real.log (z.num.natAbs : ℝ) ≤ rationalHeight z :=
    Real.log_le_log hn0 (by exact_mod_cast le_max_left z.num.natAbs z.den)
  have hld' : Real.log (z.den : ℝ) ≤ rationalHeight z :=
    Real.log_le_log hd0 (by exact_mod_cast le_max_right z.num.natAbs z.den)
  rw [hne, Real.log_div hn0.ne' hd0.ne', abs_le]
  constructor <;> linarith

theorem selected_numerator_le {N : ℕ} {ν θ w : ℝ}
    {s : ℚ} (hs : s ∈ Gate06.selectedFractions N ν θ w) :
    (s.num.natAbs : ℝ) ≤ 2 * Real.exp w ∧ (s.den : ℝ) ≤ Real.exp w := by
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hs
  have h := Gate06.selectedFraction_spec hb
  have hs0 : 0 ≤ Gate06.selectedFraction N ν θ w b := by linarith [h.1.2.2.2.1]
  have hs2 : (Gate06.selectedFraction N ν θ w b : ℝ) ≤ 2 := by
    exact_mod_cast h.1.2.2.2.2.1
  refine ⟨?_, h.2.2⟩
  rw [numerator_cast hs0]
  have hd0 : (0 : ℝ) ≤ (Gate06.selectedFraction N ν θ w b).den := by positivity
  exact (mul_le_mul_of_nonneg_right hs2 hd0).trans
    (mul_le_mul_of_nonneg_left h.2.2 (by norm_num))

theorem selected_ratio_height {N : ℕ} {ν θ w : ℝ} {s t : ℚ}
    (hs : s ∈ Gate06.selectedFractions N ν θ w)
    (ht : t ∈ Gate06.selectedFractions N ν θ w) :
    rationalHeight (t / s) ≤ 2 * w + Real.log 2 := by
  have hs0 := Gate06.selectedFractions_positive hs
  have ht0 := Gate06.selectedFractions_positive ht
  have hsB := selected_numerator_le hs
  have htB := selected_numerator_le ht
  have hden (u v : ℚ) (hu : 0 < u) (hv : 0 < v)
      (hud : (u.den : ℝ) ≤ Real.exp w) (hvn : (v.num.natAbs : ℝ) ≤ 2 * Real.exp w) :
      ((u / v).den : ℝ) ≤ 2 * Real.exp w ^ 2 := by
    have h := Gate06.product_den_le u v⁻¹
    rw [Rat.den_inv_of_ne_zero hv.ne'] at h
    have hr : ((u / v).den : ℝ) ≤ (u.den : ℝ) * v.num.natAbs := by
      exact_mod_cast h
    have hm := mul_le_mul hud hvn (by positivity : (0 : ℝ) ≤ v.num.natAbs)
      (Real.exp_pos w).le
    exact hr.trans (by nlinarith [hm])
  have hd := hden t s ht0 hs0 htB.2 hsB.1
  have hn := hden s t hs0 ht0 hsB.2 htB.1
  have he : (t / s).num.natAbs = (s / t).den := by
    rw [← Rat.den_inv_of_ne_zero (div_pos ht0 hs0).ne', inv_div]
  have hmax : ((max (t / s).num.natAbs (t / s).den : ℕ) : ℝ) ≤
      2 * Real.exp w ^ 2 := by
    rw [Nat.cast_max, he]
    exact max_le hn hd
  have hm0 : (0 : ℝ) < (max (t / s).num.natAbs (t / s).den : ℕ) := by
    exact_mod_cast (lt_of_lt_of_le (t / s).pos (le_max_right _ _))
  have hh := Real.log_le_log hm0 hmax
  dsimp [rationalHeight]
  calc
    _ ≤ Real.log (2 * Real.exp w ^ 2) := hh
    _ = 2 * w + Real.log 2 := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_exp]
      ring

theorem two_w_add_log_two_le {w : ℝ} (hw : 1 ≤ w) : 2 * w + Real.log 2 ≤ 3 * w := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

theorem selected_root_height {N q : ℕ} {ν θ w : ℝ} {s t g : ℚ}
    (hs : s ∈ Gate06.selectedFractions N ν θ w)
    (ht : t ∈ Gate06.selectedFractions N ν θ w)
    (hq : 0 < q) (hw : 1 ≤ w) (hg : 0 < g) (hne : g ≠ 1)
    (he : t / s = g ^ q) :
    Real.log 2 ≤ rationalHeight g ∧ rationalHeight g ≤ 3 * w / q ∧
      |Real.log (g : ℝ)| ≤ 3 * w / q ∧ (4 / 25 : ℝ) ≤ 3 * w / q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hh := (selected_ratio_height hs ht).trans (two_w_add_log_two_le hw)
  rw [he, rationalHeight_pow] at hh
  have hu : rationalHeight g ≤ 3 * w / q := (le_div_iff₀ hq0).mpr (by nlinarith [hh])
  have hl := log_two_le_height hg hne
  have hhalf := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at hhalf
  exact ⟨hl, hu, (abs_log_le_height hg).trans hu, by linarith⟩

/-- The entire external theorem, with one constant preceding every input.
No independence or nonzero-coefficient requirement is inserted. -/
def MatveevRationalThree : Prop :=
  ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ₁ γ₂ γ₃ : ℚ,
    0 < γ₁ → γ₁ ≠ 1 → 0 < γ₂ → γ₂ ≠ 1 → 0 < γ₃ → γ₃ ≠ 1 →
    ∀ m₁ m₂ m₃ : ℤ, ∀ A₁ A₂ A₃ : ℝ,
    rationalHeight γ₁ ≤ A₁ → |Real.log (γ₁ : ℝ)| ≤ A₁ → (4 / 25 : ℝ) ≤ A₁ →
    rationalHeight γ₂ ≤ A₂ → |Real.log (γ₂ : ℝ)| ≤ A₂ → (4 / 25 : ℝ) ≤ A₂ →
    rationalHeight γ₃ ≤ A₃ → |Real.log (γ₃ : ℝ)| ≤ A₃ → (4 / 25 : ℝ) ≤ A₃ →
    let Λ := (m₁ : ℝ) * Real.log (γ₁ : ℝ) + (m₂ : ℝ) * Real.log (γ₂ : ℝ) +
      (m₃ : ℝ) * Real.log (γ₃ : ℝ)
    let B := max 1 (max (|(m₁ : ℝ)| * A₁ / A₃)
      (max (|(m₂ : ℝ)| * A₂ / A₃) (|(m₃ : ℝ)| * A₃ / A₃)))
    Λ ≠ 0 → -C₀ * A₁ * A₂ * A₃ * (1 + Real.log B) < Real.log |Λ|

end ErdosMahlerAudit.Gate08
