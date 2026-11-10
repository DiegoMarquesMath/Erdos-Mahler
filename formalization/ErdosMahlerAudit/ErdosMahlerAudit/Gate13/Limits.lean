module

public import ErdosMahlerAudit.Gate13.Prefix

/-! Unique limits in the actual closed intervals, for one fixed tree. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate13
open Filter
open scoped Topology

noncomputable def interval (τ : ℝ) (f : List Bool → ℕ) (ε : ℕ → Bool) (n : ℕ) : Set ℝ :=
  Gate11.K τ (f («prefix» ε n))

variable {τ : ℝ} {t0 : ℕ} {f : List Bool → ℕ}

theorem interval_nonempty (ε : ℕ → Bool) (n : ℕ) : (interval τ f ε n).Nonempty :=
  Set.nonempty_Icc.mpr (Gate11.left_lt_right τ _).le

theorem interval_closed (ε : ℕ → Bool) (n : ℕ) : IsClosed (interval τ f ε n) :=
  isClosed_Icc

theorem interval_compact (ε : ℕ → Bool) (n : ℕ) : IsCompact (interval τ f ε n) :=
  isCompact_Icc

variable (hTree : Gate12.TreeSpec τ t0 f)

include hTree in
theorem interval_strict_nested (ε : ℕ → Bool) (n : ℕ) :
    interval τ f ε (n + 1) ⊆ interior (interval τ f ε n) := by
  dsimp [interval]
  rw [prefix_succ]
  have hp := hTree.pairs («prefix» ε n)
  cases h : ε n with
  | false => exact hp.left_nested
  | true => exact hp.right_nested

include hTree in
theorem interval_nested (ε : ℕ → Bool) (n : ℕ) :
    interval τ f ε (n + 1) ⊆ interval τ f ε n :=
  (interval_strict_nested hTree ε n).trans interior_subset

include hTree in
theorem interval_antitone (ε : ℕ → Bool) : Antitone (interval τ f ε) :=
  antitone_nat_of_succ_le (interval_nested hTree ε)

include hTree in
theorem interval_subset_root (ε : ℕ → Bool) (n : ℕ) :
    interval τ f ε n ⊆ Gate11.K τ t0 := by
  simpa [interval, hTree.root_eq] using interval_antitone hTree ε (Nat.zero_le n)

include hTree in
theorem branch_height (ε : ℕ → Bool) (n : ℕ) : t0 + n ≤ f («prefix» ε n) := by
  simpa using hTree.height («prefix» ε n)

include hTree in
theorem branch_width_bound (ε : ℕ → Bool) (n : ℕ) :
    Gate12.width τ (f («prefix» ε n)) ≤ Gate12.width τ t0 / (81 : ℝ) ^ n := by
  simpa using hTree.decay («prefix» ε n)

theorem width_bound_formula (τ : ℝ) (t0 n : ℕ) :
    Gate12.width τ t0 / (81 : ℝ) ^ n =
      2 * (3 : ℝ) ^ (-τ * (t0 : ℝ)) / (81 : ℝ) ^ n := by
  rw [Gate12.width, Gate11.width_eq]
  rfl

theorem width_bound_pos (τ : ℝ) (t0 n : ℕ) :
    0 < Gate12.width τ t0 / (81 : ℝ) ^ n :=
  div_pos (Gate12.width_pos τ t0) (Gate12.decay_denominator_pos n)

theorem width_bound_tendsto (τ : ℝ) (t0 : ℕ) :
    Tendsto (fun n : ℕ => Gate12.width τ t0 / (81 : ℝ) ^ n) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 81⁻¹) (by norm_num : (81 : ℝ)⁻¹ < 1)).const_mul
      (Gate12.width τ t0)
  simpa only [mul_zero, inv_pow, div_eq_mul_inv] using h

theorem width_bound_small (τ : ℝ) (t0 : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, Gate12.width τ t0 / (81 : ℝ) ^ n < δ := by
  exact ((width_bound_tendsto τ t0).eventually (gt_mem_nhds hδ)).exists

include hTree in
theorem interval_distance {ε : ℕ → Bool} {n : ℕ} {x y : ℝ}
    (hx : x ∈ interval τ f ε n) (hy : y ∈ interval τ f ε n) :
    |x - y| ≤ Gate12.width τ t0 / (81 : ℝ) ^ n := by
  apply le_trans _ (branch_width_bound hTree ε n)
  change |x - y| ≤ Gate11.right τ _ - Gate11.left τ _
  change Gate11.left τ _ ≤ x ∧ x ≤ Gate11.right τ _ at hx
  change Gate11.left τ _ ≤ y ∧ y ≤ Gate11.right τ _ at hy
  exact abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hy.1, hx.2]⟩

include hTree in
theorem unique_limit (ε : ℕ → Bool) : ∃! x : ℝ, ∀ n, x ∈ interval τ f ε n := by
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (interval τ f ε) (interval_nested hTree ε) (interval_nonempty ε)
    (interval_compact ε 0) (interval_closed ε)
  have hx' : ∀ n, x ∈ interval τ f ε n := Set.mem_iInter.mp hx
  refine ⟨x, hx', ?_⟩
  intro y hy
  apply sub_eq_zero.mp
  apply abs_eq_zero.mp
  apply le_antisymm _ (abs_nonneg _)
  by_contra h
  have hpos : 0 < |y - x| := lt_of_not_ge h
  obtain ⟨n, hn⟩ := width_bound_small τ t0 hpos
  exact (not_lt_of_ge (interval_distance hTree (hy n) (hx' n))) hn

noncomputable def point (ε : ℕ → Bool) : ℝ := (unique_limit hTree ε).choose

theorem point_mem (ε : ℕ → Bool) (n : ℕ) : point hTree ε ∈ interval τ f ε n :=
  (unique_limit hTree ε).choose_spec.1 n

theorem point_interior (ε : ℕ → Bool) (n : ℕ) :
    point hTree ε ∈ interior (Gate11.K τ (f («prefix» ε n))) :=
  interval_strict_nested hTree ε n (point_mem hTree ε (n + 1))

theorem point_endpoints (ε : ℕ → Bool) (n : ℕ) :
    Gate11.left τ (f («prefix» ε n)) < point hTree ε ∧
      point hTree ε < Gate11.right τ (f («prefix» ε n)) := by
  simpa only [Gate11.interior_K, Set.mem_Ioo] using point_interior hTree ε n

theorem point_displacement (ε : ℕ → Bool) (n : ℕ) :
    (3 : ℝ) ^ (-τ * (f («prefix» ε n) : ℝ)) < point hTree ε - (R (f («prefix» ε n)) : ℝ) ∧
    point hTree ε - (R (f («prefix» ε n)) : ℝ) <
      3 * (3 : ℝ) ^ (-τ * (f («prefix» ε n) : ℝ)) := by
  have h := point_endpoints hTree ε n
  dsimp [Gate11.left, Gate11.right, Gate02.radius] at h
  constructor <;> linarith [h.1, h.2]

theorem point_prefix_bound (ε η : ℕ → Bool) (n : ℕ) (h : «prefix» ε n = «prefix» η n) :
    |point hTree ε - point hTree η| ≤ Gate12.width τ t0 / (81 : ℝ) ^ n := by
  apply interval_distance hTree (point_mem hTree ε n)
  simpa only [interval, h] using point_mem hTree η n

theorem point_agreement_bound (ε η : ℕ → Bool) (n : ℕ)
    (h : ∀ i < n, ε i = η i) :
    |point hTree ε - point hTree η| ≤ Gate12.width τ t0 / (81 : ℝ) ^ n :=
  point_prefix_bound hTree ε η n ((prefix_eq_iff ε η n).2 h)

end ErdosMahlerAudit.Gate13
