module

public import ErdosMahlerAudit.Gate03.Approximation
public import ErdosMahlerAudit.Gate02.Density
public import Mathlib.Data.Int.Interval

/-! Translated-grid counting by integer lifts. Floors of the actual orbit
points select the lifts, so the argument includes wraparound and endpoints.
The final discrepancy statement here is for real open intervals in [0,1]. -/

public section
namespace ErdosMahlerAudit.Gate03

/-- An injective integer-valued map into a closed real interval bounds cardinality. -/
theorem card_le_of_integer_lifts (s : Finset ℕ) (f : ℕ → ℤ) (L U : ℝ)
    (hLU : L ≤ U) (hf : Set.InjOn f s)
    (hbound : ∀ b ∈ s, L ≤ (f b : ℝ) ∧ (f b : ℝ) ≤ U) :
    (s.card : ℝ) ≤ U - L + 1 := by
  have hcard : s.card ≤ (Finset.Icc ⌈L⌉ ⌊U⌋).card := by
    apply Finset.card_le_card_of_injOn f _ hf
    intro b hb
    exact Finset.mem_Icc.mpr ⟨Int.ceil_le.mpr (hbound b hb).1,
      Int.le_floor.mpr (hbound b hb).2⟩
  by_cases h : ⌈L⌉ ≤ ⌊U⌋ + 1
  · have he := Int.card_Icc_of_le _ _ h
    have her : ((Finset.Icc ⌈L⌉ ⌊U⌋).card : ℝ) = (⌊U⌋ : ℝ) + 1 - ⌈L⌉ := by
      exact_mod_cast he
    have hc : (s.card : ℝ) ≤ (Finset.Icc ⌈L⌉ ⌊U⌋).card := by exact_mod_cast hcard
    rw [her] at hc
    have := Int.floor_le U
    have := Int.le_ceil L
    linarith
  · have hempty : Finset.Icc ⌈L⌉ ⌊U⌋ = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hempty, Finset.card_empty] at hcard
    have : s.card = 0 := Nat.eq_zero_of_le_zero hcard
    simp only [this, Nat.cast_zero]
    linarith

/-- Coprimality makes all integer lifts distinct within a block of length N.
The integer adjustment z is arbitrary; this includes all wraparound choices. -/
theorem grid_lift_injective {N : ℕ} {p : ℤ} (hcop : Nat.Coprime p.natAbs N)
    (z : ℕ → ℤ) :
    Set.InjOn (fun b : ℕ => p*((b : ℤ)-N) - N*z b) (Finset.Ico N (2*N)) := by
  intro b hb c hc he
  have hb' := Finset.mem_Ico.mp hb
  have hc' := Finset.mem_Ico.mp hc
  have hd : (N : ℤ) ∣ p*((b : ℤ)-c) := by
    refine ⟨z b-z c, ?_⟩
    linear_combination he
  have hg : Int.gcd (N : ℤ) p = 1 := by
    simpa [Int.gcd_def] using hcop.symm.gcd_eq_one
  have hd' := Int.dvd_of_dvd_mul_right_of_gcd_one hd hg
  have habs : |(b : ℤ)-c| < (N : ℤ) := abs_lt.mpr ⟨by omega, by omega⟩
  have heq := Int.eq_zero_of_abs_lt_dvd hd' habs
  omega

/-- Any subset of the actual block whose fractional parts lie in [l,r]
has cardinality at most N*(r-l)+3. This also works when l or r is 0 or 1. -/
theorem rotation_closed_upper {N : ℕ} (hN : N ∈ convergentDenominators)
    (s : Finset ℕ) (hs : s ⊆ Finset.Ico N (2 * N)) (l r : ℝ) (hlr : l ≤ r)
    (hmem : ∀ b ∈ s, l ≤ Int.fract ((b : ℝ) * alpha) ∧
      Int.fract ((b : ℝ) * alpha) ≤ r) :
    (s.card : ℝ) ≤ (N : ℝ)*(r-l)+3 := by
  obtain ⟨p, hcop, herr⟩ := translated_grid_error hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast convergentDenominators_pos hN
  let z : ℕ → ℤ := fun b => ⌊(b : ℝ)*alpha⌋
  let f : ℕ → ℤ := fun b => p*((b : ℤ)-N) - N*z b
  let T : ℝ := (N : ℝ)*((N : ℝ)*alpha)
  have hinj : Set.InjOn f s := (grid_lift_injective hcop z).mono hs
  have hbound : ∀ b ∈ s, (N : ℝ)*l-T-1 ≤ (f b : ℝ) ∧
      (f b : ℝ) ≤ (N : ℝ)*r-T+1 := by
    intro b hb
    have hbN := Finset.mem_Ico.mp (hs hb)
    have hi : b-N < N := by omega
    have hbi : N+(b-N) = b := Nat.add_sub_of_le hbN.1
    have he := herr (b-N) hi
    rw [hbi, Nat.cast_sub hbN.1] at he
    have he' : |(N : ℝ)*Int.fract ((b : ℝ)*alpha) - (T+(f b : ℝ))| < 1 := by
      have hmul := mul_lt_mul_of_pos_left he hNr
      rw [mul_one_div_cancel hNr.ne'] at hmul
      have hmul' : |(N : ℝ)*((b : ℝ)*alpha -
          ((N : ℝ)*alpha + ((b : ℝ)-N)*p/N))| < 1 := by
        rw [abs_mul, abs_of_pos hNr]
        exact hmul
      have hid : (N : ℝ)*Int.fract ((b : ℝ)*alpha) - (T+(f b : ℝ)) =
          (N : ℝ)*((b : ℝ)*alpha - ((N : ℝ)*alpha + ((b : ℝ)-N)*p/N)) := by
        simp only [T, f, z, Int.fract, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
        field_simp
        ring
      rw [hid]
      exact hmul'
    obtain ⟨he1, he2⟩ := abs_lt.mp he'
    obtain ⟨hl, hr⟩ := hmem b hb
    have hl' := mul_le_mul_of_nonneg_left hl hNr.le
    have hr' := mul_le_mul_of_nonneg_left hr hNr.le
    constructor <;> linarith
  have hLU : (N : ℝ)*l-T-1 ≤ (N : ℝ)*r-T+1 := by nlinarith
  have h := card_le_of_integer_lifts s f _ _ hLU hinj hbound
  nlinarith

/-- The actual block filtered by an open real interval of fractional parts. -/
@[expose] noncomputable def openRotationIndices (N : ℕ) (l r : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Ico N (2*N)).filter (fun b => l < Int.fract ((b : ℝ)*alpha) ∧
    Int.fract ((b : ℝ)*alpha) < r)

/-- One absolute discrepancy constant for all open intervals inside [0,1]. -/
theorem rotation_open_discrepancy {N : ℕ} (hN : N ∈ convergentDenominators)
    (l r : ℝ) (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ 1) :
    |((openRotationIndices N l r).card : ℝ) - (N : ℝ)*(r-l)| ≤ 6 := by
  classical
  let S := Finset.Ico N (2*N)
  let C := openRotationIndices N l r
  let L := S.filter (fun b : ℕ => Int.fract ((b : ℝ)*alpha) ≤ l)
  let U := S.filter (fun b : ℕ => r ≤ Int.fract ((b : ℝ)*alpha))
  have hC : (C.card : ℝ) ≤ (N : ℝ)*(r-l)+3 :=
    rotation_closed_upper hN C (Finset.filter_subset _ _) l r hlr (by
      intro b hb
      obtain ⟨_, hb⟩ := Finset.mem_filter.mp hb
      exact ⟨hb.1.le, hb.2.le⟩)
  have hL : (L.card : ℝ) ≤ (N : ℝ)*l+3 := by
    have h := rotation_closed_upper hN L (Finset.filter_subset _ _) 0 l hl (by
      intro b hb
      exact ⟨Int.fract_nonneg _, (Finset.mem_filter.mp hb).2⟩)
    simpa using h
  have hU : (U.card : ℝ) ≤ (N : ℝ)*(1-r)+3 :=
    rotation_closed_upper hN U (Finset.filter_subset _ _) r 1 hr (by
      intro b hb
      exact ⟨(Finset.mem_filter.mp hb).2, (Int.fract_lt_one _).le⟩)
  have hcover : S ⊆ C ∪ L ∪ U := by
    intro b hb
    by_cases hlo : l < Int.fract ((b : ℝ)*alpha)
    · by_cases hhi : Int.fract ((b : ℝ)*alpha) < r
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hb, hlo, hhi⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hb, le_of_not_gt hhi⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hb, le_of_not_gt hlo⟩))
  have hsum : S.card ≤ C.card + L.card + U.card :=
    (Finset.card_le_card hcover).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hScard : S.card = N := by dsimp [S]; rw [Nat.card_Ico]; omega
  rw [hScard] at hsum
  have hsumr : (N : ℝ) ≤ (C.card : ℝ) + (L.card : ℝ) + (U.card : ℝ) := by
    exact_mod_cast hsum
  apply abs_le.mpr
  change -6 ≤ (C.card : ℝ)-(N : ℝ)*(r-l) ∧ (C.card : ℝ)-(N : ℝ)*(r-l) ≤ 6
  constructor <;> nlinarith

/-- Phi is injective on the positive real domain, which includes every J and R(b). -/
theorem Phi_injOn_positive : Set.InjOn Phi (Set.Ioi 0) := by
  intro x hx y hy h
  apply Real.log_injOn_pos hx hy
  apply (div_left_inj' (ne_of_gt log_two_pos)).mp
  dsimp [Phi] at h
  linarith

/-- The image endpoints are strictly inside (0,1), including at tau=4. -/
theorem Phi_J_endpoints {t : ℕ} {τ : ℝ} (ht : 0 < t) (hτ : 4 ≤ τ) :
    0 < Phi ((R t : ℝ)+2*Gate02.radius t τ) ∧
    Phi ((R t : ℝ)+2*Gate02.radius t τ) < Phi ((R t : ℝ)+Gate02.radius t τ) ∧
    Phi ((R t : ℝ)+Gate02.radius t τ) < 1 := by
  have hR := R_mem_Ioo ht
  have hrad := Gate02.radius_pos t τ
  have hupper := Gate02.interval_upper ht hτ
  have hlo : 1 < (R t : ℝ)+Gate02.radius t τ := by linarith
  have hlogpos := Real.log_pos hlo
  have hloglt := Real.log_lt_log (by linarith : 0 < (R t : ℝ)+2*Gate02.radius t τ) hupper
  have hdiv := (div_lt_one log_two_pos).mpr hloglt
  have hposdiv := div_pos hlogpos log_two_pos
  have hgap := Gate02.rho_pos t τ
  dsimp [Gate02.rho, Phi] at *
  exact ⟨by linarith, by linarith, by linarith⟩

/-- Exact identification using the already-proved Phi_R and Phi_image_J. -/
theorem candidateIndices_eq_openRotationIndices {N t : ℕ} {τ : ℝ}
    (hN : N ∈ convergentDenominators) (ht : 0 < t) (hτ : 4 ≤ τ) :
    Gate02.candidateIndices t τ N = openRotationIndices N
      (Phi ((R t : ℝ)+2*Gate02.radius t τ)) (Phi ((R t : ℝ)+Gate02.radius t τ)) := by
  classical
  apply Finset.ext
  intro b
  simp only [Gate02.candidateIndices, openRotationIndices, Finset.mem_filter]
  constructor
  · rintro ⟨hb, hJ⟩
    have hbpos : 0 < b := (convergentDenominators_pos hN).trans_le (Finset.mem_Ico.mp hb).1
    refine ⟨hb, ?_⟩
    have him : Phi (R b) ∈ Phi '' Gate02.J t τ := ⟨R b, hJ, rfl⟩
    rw [Gate02.Phi_image_J, Phi_R hbpos] at him
    exact him
  · rintro ⟨hb, hphi⟩
    have hbpos : 0 < b := (convergentDenominators_pos hN).trans_le (Finset.mem_Ico.mp hb).1
    have him : Phi (R b) ∈ Phi '' Gate02.J t τ := by
      rw [Gate02.Phi_image_J, Phi_R hbpos]
      exact hphi
    obtain ⟨x, hx, he⟩ := him
    have hxpos : 0 < x := lt_trans (by norm_num) ((Gate02.J_subset_Ioo ht hτ) hx).1
    have hRbpos : (0 : ℝ) < R b := by exact_mod_cast R_pos b
    have hxeq : x = (R b : ℝ) := Phi_injOn_positive hxpos hRbpos he
    exact ⟨hb, hxeq ▸ hx⟩

/-- The exact Gate 02 rotation conclusion, with constant 6 for every parameter. -/
theorem candidate_discrepancy {N t : ℕ} {τ : ℝ}
    (hN : N ∈ convergentDenominators) (ht : 0 < t) (hτ : 4 ≤ τ) :
    |((Gate02.candidateIndices t τ N).card : ℝ) - (N : ℝ)*Gate02.rho t τ| ≤ 6 := by
  obtain ⟨hl, hlr, hr⟩ := Phi_J_endpoints ht hτ
  rw [candidateIndices_eq_openRotationIndices hN ht hτ]
  exact rotation_open_discrepancy hN _ _ hl.le hlr.le hr.le

/-- The absolute constant precedes tau, the parent, and the block height. -/
theorem rotation_uniform : ∃ Crot : ℝ, 0 ≤ Crot ∧
    ∀ τ : ℝ, 4 ≤ τ → ∀ t : ℕ, 0 < t → ∀ N : ℕ, N ∈ convergentDenominators →
      |((Gate02.candidateIndices t τ N).card : ℝ) - (N : ℝ)*Gate02.rho t τ| ≤ Crot :=
  ⟨6, by norm_num, fun _ hτ _ ht _ hN => candidate_discrepancy hN ht hτ⟩

end ErdosMahlerAudit.Gate03
