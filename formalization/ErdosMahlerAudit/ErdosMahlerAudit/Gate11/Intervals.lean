module

public import ErdosMahlerAudit.Gate02.Density

/-! The closed intervals in the frozen construction (TeX 213–223, 288–306).
The radius is exactly Gate 02's real power, including at τ = 4. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate11

noncomputable def left (τ : ℝ) (t : ℕ) : ℝ := (R t : ℝ) + Gate02.radius t τ

noncomputable def right (τ : ℝ) (t : ℕ) : ℝ := (R t : ℝ) + 3 * Gate02.radius t τ

noncomputable def K (τ : ℝ) (t : ℕ) : Set ℝ := Set.Icc (left τ t) (right τ t)

theorem J_eq (τ : ℝ) (t : ℕ) :
    Gate02.J t τ = Set.Ioo (left τ t) ((R t : ℝ) + 2 * Gate02.radius t τ) := rfl

theorem left_lt_right (τ : ℝ) (t : ℕ) : left τ t < right τ t := by
  have := Gate02.radius_pos t τ
  dsimp [left, right]
  linarith

theorem interior_K (τ : ℝ) (t : ℕ) :
    interior (K τ t) = Set.Ioo (left τ t) (right τ t) := by
  exact interior_Icc

theorem width_eq (τ : ℝ) (t : ℕ) :
    right τ t - left τ t = 2 * Gate02.radius t τ := by
  dsimp [right, left]
  ring

/-- One integer step gives a factor at most 3⁻⁴, uniformly for all τ ≥ 4. -/
theorem radius_decay {τ : ℝ} {t d : ℕ} (hτ : 4 ≤ τ) (htd : t < d) :
    Gate02.radius d τ ≤ Gate02.radius t τ / 81 := by
  have hd : (t : ℝ) + 1 ≤ d := by exact_mod_cast htd
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
    (show -τ * (d : ℝ) ≤ -τ * (t : ℝ) + (-4) by nlinarith)
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)] at h
  norm_num [Gate02.radius, Real.rpow_neg] at h ⊢
  linarith

theorem radius_strictAnti {τ : ℝ} (hτ : 4 ≤ τ) :
    StrictAnti (fun t : ℕ => Gate02.radius t τ) := by
  intro t d htd
  have := radius_decay hτ htd
  have := Gate02.radius_pos t τ
  linarith

/-- The fourth-power bound is strong enough both for the domain and separation. -/
theorem radius_le_fourth {τ : ℝ} (t : ℕ) (hτ : 4 ≤ τ) :
    Gate02.radius t τ ≤ 1 / ((3 : ℝ) ^ t) ^ 4 := by
  rw [Gate02.radius_eq_Q]
  have h := Real.rpow_le_rpow_of_exponent_le
    (show (1 : ℝ) ≤ (3 : ℝ) ^ t from one_le_pow₀ (by norm_num)) (neg_le_neg hτ)
  simpa only [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 3 ^ t),
    Real.rpow_ofNat, one_div] using h

theorem radius_extension_lt {τ : ℝ} {t : ℕ} (ht : 0 < t) (hτ : 4 ≤ τ) :
    3 * Gate02.radius t τ < 1 / ((3 : ℝ) ^ t) ^ 2 := by
  have hQ := Gate02.three_le_Q ht
  have hp : (0 : ℝ) < (3 : ℝ) ^ t := by positivity
  have hs : 3 / ((3 : ℝ) ^ t) ^ 4 < 1 / ((3 : ℝ) ^ t) ^ 2 := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg ((3 : ℝ) ^ t - 3), sq_pos_of_pos hp]
  have hr := radius_le_fourth t hτ
  simp only [div_eq_mul_inv] at hr hs ⊢
  linarith

theorem endpoints_mem_Ioo {τ : ℝ} {t : ℕ} (ht : 0 < t) (hτ : 4 ≤ τ) :
    1 < left τ t ∧ right τ t < 2 := by
  have hR := R_mem_Ioo ht
  have hr := Gate02.radius_pos t τ
  have hu := Gate02.R_le_two_sub_inv ht
  have he := radius_extension_lt ht hτ
  have hQ := Gate02.three_le_Q ht
  have hp : (0 : ℝ) < (3 : ℝ) ^ t := by positivity
  have hi : 1 / ((3 : ℝ) ^ t) ^ 2 ≤ 1 / (3 : ℝ) ^ t := by
    apply (div_le_div_iff₀ (by positivity) hp).mpr
    nlinarith
  dsimp [left, right]
  constructor <;> linarith

theorem K_subset_Ioo {τ : ℝ} {t : ℕ} (ht : 0 < t) (hτ : 4 ≤ τ) :
    K τ t ⊆ Set.Ioo 1 2 := by
  intro x hx
  have he := endpoints_mem_Ioo ht hτ
  exact ⟨he.1.trans_le hx.1, hx.2.trans_lt he.2⟩

/-- Both endpoint inequalities control the entire closed child interval. -/
theorem nested_endpoints {τ : ℝ} {t d : ℕ} (hτ : 4 ≤ τ) (htd : t < d)
    (hJ : (R d : ℝ) ∈ Gate02.J t τ) :
    left τ t < left τ d ∧ right τ d < right τ t := by
  have hd := Gate02.radius_pos d τ
  have ht := Gate02.radius_pos t τ
  have hdec := radius_decay hτ htd
  change (R t : ℝ) + Gate02.radius t τ < (R d : ℝ) ∧
    (R d : ℝ) < (R t : ℝ) + 2 * Gate02.radius t τ at hJ
  dsimp [left, right]
  constructor <;> linarith [hJ.1, hJ.2]

theorem K_subset_interior {τ : ℝ} {t d : ℕ} (hτ : 4 ≤ τ) (htd : t < d)
    (hJ : (R d : ℝ) ∈ Gate02.J t τ) : K τ d ⊆ interior (K τ t) := by
  rw [interior_K]
  intro x hx
  have he := nested_endpoints hτ htd hJ
  exact ⟨he.1.trans_le hx.1, hx.2.trans_lt he.2⟩

theorem width_contraction {τ : ℝ} {t d : ℕ} (hτ : 4 ≤ τ) (htd : t < d) :
    right τ d - left τ d ≤ (right τ t - left τ t) / 81 ∧
    right τ d - left τ d < right τ t - left τ t := by
  rw [width_eq, width_eq]
  have := radius_decay hτ htd
  have := radius_strictAnti hτ htd
  constructor <;> linarith

end ErdosMahlerAudit.Gate11
