module

public import ErdosMahlerAudit.Gate05.EscapingDenominators
public import ErdosMahlerAudit.Gate03.Denominators
public import Mathlib.Data.Finset.Lattice.Fold

/-! The actual finite maximum W_N, including denominator-one witnesses. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate05
open Filter
open scoped Topology

theorem exceptional_den_lt_three_pow {b : ℕ} {ν : ℝ} {s : ℚ}
    (hs : Exceptional b ν s) : s.den < 3 ^ b := by
  have hv1 : (1 : ℝ) ≤ s.den := by exact_mod_cast s.pos
  have hv : (0 : ℝ) < s.den := by exact_mod_cast s.pos
  have hν := hs.2.1
  have hp : (s.den : ℝ) ≤ (s.den : ℝ) ^ (ν - 1) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hv1 (by linarith : (1 : ℝ) ≤ ν - 1)
  have he := exceptional_den_bound hs
  have h : (s.den : ℝ) < (3 : ℝ) ^ b := by nlinarith
  exact_mod_cast h

noncomputable def exceptionalDenominators (N : ℕ) (ν : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (3 ^ (2 * N))).filter (fun k =>
    ∃ b : ℕ, N ≤ b ∧ b < 2 * N ∧ ∃ s : ℚ, Exceptional b ν s ∧ s.den = k)

theorem mem_exceptionalDenominators {N k : ℕ} {ν : ℝ} :
    k ∈ exceptionalDenominators N ν ↔
      ∃ b : ℕ, N ≤ b ∧ b < 2 * N ∧ ∃ s : ℚ, Exceptional b ν s ∧ s.den = k := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · rintro ⟨b, hb1, hb, s, hs, rfl⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, b, hb1, hb, s, hs, rfl⟩
    exact (exceptional_den_lt_three_pow hs).trans_le (pow_le_pow_right₀ (by norm_num) hb.le)

noncomputable def logarithmicHeight (N : ℕ) (ν : ℝ) : ℝ :=
  Real.log ((max 1 ((exceptionalDenominators N ν).sup id) : ℕ) : ℝ)

theorem logarithmicHeight_nonneg (N : ℕ) (ν : ℝ) : 0 ≤ logarithmicHeight N ν := by
  apply Real.log_nonneg
  exact_mod_cast (le_max_left 1 ((exceptionalDenominators N ν).sup id))

theorem witness_log_le_height {N b : ℕ} {ν : ℝ} {s : ℚ}
    (hb : N ≤ b) (hb2 : b < 2 * N) (hs : Exceptional b ν s) :
    Real.log (s.den : ℝ) ≤ logarithmicHeight N ν := by
  have hm := mem_exceptionalDenominators.mpr ⟨b, hb, hb2, s, hs, rfl⟩
  apply Real.log_le_log (by exact_mod_cast s.pos)
  exact_mod_cast ((Finset.le_sup (f := id) hm).trans (le_max_right 1 _))

theorem logarithmicHeight_eq_zero_or_witness (N : ℕ) (ν : ℝ) :
    logarithmicHeight N ν = 0 ∨ ∃ b : ℕ, N ≤ b ∧ b < 2 * N ∧
      ∃ s : ℚ, Exceptional b ν s ∧ logarithmicHeight N ν = Real.log (s.den : ℝ) := by
  classical
  by_cases hempty : exceptionalDenominators N ν = ∅
  · left; simp [logarithmicHeight, hempty]
  · obtain ⟨k, hk, hsup⟩ := Finset.exists_mem_eq_sup (exceptionalDenominators N ν)
      (Finset.nonempty_iff_ne_empty.mpr hempty) id
    obtain ⟨b, hb, hb2, s, hs, hden⟩ := mem_exceptionalDenominators.mp hk
    right
    refine ⟨b, hb, hb2, s, hs, ?_⟩
    simp only [logarithmicHeight, hsup, id_eq, ← hden, max_eq_right (Nat.succ_le_of_lt s.pos)]

theorem logarithmicHeight_le {N : ℕ} {ν C : ℝ} (hC : 0 ≤ C)
    (h : ∀ b : ℕ, N ≤ b → b < 2 * N → ∀ s : ℚ, Exceptional b ν s →
      Real.log (s.den : ℝ) ≤ C) : logarithmicHeight N ν ≤ C := by
  rcases logarithmicHeight_eq_zero_or_witness N ν with he | ⟨b, hb, hb2, s, hs, he⟩
  · rwa [he]
  · rw [he]; exact h b hb hb2 s hs

/-- Zero height permits witnesses of denominator one. -/
theorem logarithmicHeight_zero_iff (N : ℕ) (ν : ℝ) :
    logarithmicHeight N ν = 0 ↔ ∀ b : ℕ, N ≤ b → b < 2 * N →
      ∀ s : ℚ, Exceptional b ν s → s.den = 1 := by
  constructor
  · intro h b hb hb2 s hs
    have hl := witness_log_le_height hb hb2 hs
    rw [h] at hl
    have hn : 0 ≤ Real.log (s.den : ℝ) := Real.log_nonneg (by exact_mod_cast s.pos)
    exact_mod_cast Real.eq_one_of_pos_of_log_eq_zero (by exact_mod_cast s.pos)
      (le_antisymm hl hn)
  · intro h
    apply le_antisymm (logarithmicHeight_le le_rfl ?_) (logarithmicHeight_nonneg N ν)
    intro b hb hb2 s hs
    simp only [h b hb hb2 s hs, Nat.cast_one, Real.log_one, le_refl]

theorem E_one_eq_zero_of_height_zero {N : ℕ} {ν : ℝ}
    (h : logarithmicHeight N ν = 0) : Gate02.E N 1 ν = 0 := by
  classical
  have hempty : Gate02.badIndices N 1 ν = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro b hb
    obtain ⟨hb, hb2, s, hs, hden⟩ := Gate02.mem_badIndices.mp hb
    rw [(logarithmicHeight_zero_iff N ν).mp h b hb hb2 s hs] at hden
    norm_num at hden
  simp only [Gate02.E, hempty, Finset.card_empty]

theorem logarithmicHeight_sublinear (hST : SubspaceTwoThreePrimitive)
    (ν : ℝ) (hν : 4 < ν) (hν5 : ν ≤ 5) :
    ∀ η : ℝ, 0 < η → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → N ∈ convergentDenominators →
      logarithmicHeight N ν ≤ η * (N : ℝ) := by
  intro η hη
  obtain ⟨N0, hN0⟩ := exceptional_log_sublinear hST ν hν hν5 η hη
  exact ⟨N0, fun N hN hND => logarithmicHeight_le
    (mul_nonneg hη.le (Nat.cast_nonneg N)) (hN0 N hN hND)⟩

theorem logarithmicHeight_div_tendsto_zero (hST : SubspaceTwoThreePrimitive)
    (ν : ℝ) (hν : 4 < ν) (hν5 : ν ≤ 5) :
    Tendsto (fun N : ℕ => logarithmicHeight N ν / (N : ℝ))
      (atTop ⊓ 𝓟 convergentDenominators) (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro r hr
    exact Filter.Eventually.of_forall (fun N => hr.trans_le
      (div_nonneg (logarithmicHeight_nonneg N ν) (Nat.cast_nonneg N)))
  · intro r hr
    obtain ⟨N0, hN0⟩ := logarithmicHeight_sublinear hST ν hν hν5 (r / 2) (by linarith)
    apply eventually_inf_principal.mpr
    filter_upwards [eventually_ge_atTop N0] with N hN hND
    have hNp : (0 : ℝ) < N := by exact_mod_cast Gate03.convergentDenominators_pos hND
    have h := (div_le_iff₀ hNp).mpr (hN0 N hN hND)
    exact h.trans_lt (by linarith : r / 2 < r)

end ErdosMahlerAudit.Gate05
