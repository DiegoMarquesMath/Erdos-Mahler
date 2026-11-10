module

public import ErdosMahlerAudit.Gate04.RationalGrid
public import Mathlib.Data.Nat.Factorization.Basic

/-! Canonical arithmetic in Lemma 3.2, TeX 569–579. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate05

noncomputable def P (b : ℕ) : ℕ := 2 ^ a b
def S (b : ℕ) : ℕ := 3 ^ b
def u (s : ℚ) : ℕ := s.num.natAbs
def v (s : ℚ) : ℕ := s.den
noncomputable def d (b : ℕ) (s : ℚ) : ℕ := Nat.gcd (P b * v s) (S b * u s)
noncomputable def U (b : ℕ) (s : ℚ) : ℕ := P b * v s / d b s
noncomputable def W (b : ℕ) (s : ℚ) : ℕ := S b * u s / d b s
noncomputable def e (b : ℕ) (s : ℚ) : ℕ :=
  ((P b * v s : ℕ) - (S b * u s : ℕ) : ℤ).natAbs
noncomputable def H (b : ℕ) (s : ℚ) : ℕ := max (U b s) (W b s)

theorem P_pos (b : ℕ) : 0 < P b := by unfold P; positivity
theorem S_pos (b : ℕ) : 0 < S b := by unfold S; positivity
theorem v_pos (s : ℚ) : 0 < v s := s.pos

theorem u_cast {s : ℚ} (hs : 1 ≤ s) : (u s : ℤ) = s.num :=
  Int.natAbs_of_nonneg (Rat.num_nonneg.mpr (by linarith))

theorem u_pos {s : ℚ} (hs : 1 ≤ s) : 0 < u s := by
  have hn : 0 < s.num := Rat.num_pos.mpr (by linarith)
  have : (0 : ℤ) < u s := by rw [u_cast hs]; exact hn
  exact_mod_cast this

theorem uv_coprime (s : ℚ) : Nat.Coprime (u s) (v s) := s.reduced

theorem canonical_real {s : ℚ} (hs : 1 ≤ s) :
    (s : ℝ) = (u s : ℝ) / v s := by
  have hu : (u s : ℝ) = (s.num : ℝ) := by exact_mod_cast u_cast hs
  rw [Rat.cast_def, hu]; rfl

theorem u_le_two_v {s : ℚ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) : u s ≤ 2 * v s := by
  have hu := (Gate04.canonical_num_bounds hs1 hs2).2.2
  have he : (u s : ℝ) = (s.num : ℝ) := by exact_mod_cast u_cast hs1
  rw [← he] at hu
  exact_mod_cast hu

theorem R_eq_P_div_S (b : ℕ) : (R b : ℝ) = (P b : ℝ) / S b := by
  simp [R_cast, P, S]

theorem S_lt_P_lt_two_S {b : ℕ} (hb : 0 < b) : S b < P b ∧ P b < 2 * S b := by
  have hS : (0 : ℝ) < S b := by exact_mod_cast S_pos b
  have hR := R_mem_Ioo hb
  rw [R_eq_P_div_S, lt_div_iff₀ hS, div_lt_iff₀ hS] at hR
  exact_mod_cast (by simpa using hR : (S b : ℝ) < P b ∧ (P b : ℝ) < 2 * S b)

theorem d_pos (b : ℕ) (s : ℚ) : 0 < d b s :=
  Nat.gcd_pos_of_pos_left _ (Nat.mul_pos (P_pos b) (v_pos s))

theorem U_pos (b : ℕ) (s : ℚ) : 0 < U b s :=
  Nat.div_gcd_pos_of_pos_left _ (Nat.mul_pos (P_pos b) (v_pos s))

theorem W_pos (b : ℕ) {s : ℚ} (hs : 1 ≤ s) : 0 < W b s :=
  Nat.div_gcd_pos_of_pos_right _ (Nat.mul_pos (S_pos b) (u_pos hs))

theorem UW_coprime (b : ℕ) (s : ℚ) : Nat.Coprime (U b s) (W b s) :=
  Nat.coprime_div_gcd_div_gcd (d_pos b s)

theorem d_mul_U (b : ℕ) (s : ℚ) : d b s * U b s = P b * v s := by
  exact Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)

theorem d_mul_W (b : ℕ) (s : ℚ) : d b s * W b s = S b * u s := by
  exact Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)

theorem d_prime_support (b : ℕ) (s : ℚ) {p : ℕ} (hp : p.Prime)
    (hpd : p ∣ d b s) : p = 2 ∨ p = 3 := by
  have hl := hp.dvd_or_dvd (hpd.trans (Nat.gcd_dvd_left (P b * v s) (S b * u s)))
  have hr := hp.dvd_or_dvd (hpd.trans (Nat.gcd_dvd_right (P b * v s) (S b * u s)))
  rcases hl with hP | hv
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp
      (hp.dvd_of_dvd_pow hP))
  · rcases hr with hS | hu
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp
        (hp.dvd_of_dvd_pow hS))
    · exact False.elim (Nat.not_coprime_of_dvd_of_dvd hp.one_lt hu hv (uv_coprime s))

theorem cross_ne {b : ℕ} {s : ℚ} (hs : 1 ≤ s) (hne : s ≠ R b) :
    P b * v s ≠ S b * u s := by
  intro he
  apply hne
  apply Rat.cast_injective (α := ℝ)
  rw [canonical_real hs, R_eq_P_div_S]
  apply (div_eq_div_iff (by exact_mod_cast (v_pos s).ne')
    (by exact_mod_cast (S_pos b).ne')).mpr
  have her : (P b : ℝ) * v s = (S b : ℝ) * u s := by exact_mod_cast he
  nlinarith

theorem e_pos {b : ℕ} {s : ℚ} (hs : 1 ≤ s) (hne : s ≠ R b) : 0 < e b s := by
  have hn : ((P b * v s : ℕ) : ℤ) - ((S b * u s : ℕ) : ℤ) ≠ 0 := by
    intro h; exact cross_ne hs hne (by exact_mod_cast sub_eq_zero.mp h)
  exact Int.natAbs_pos.mpr hn

theorem U_ne_W {b : ℕ} {s : ℚ} (hs : 1 ≤ s) (hne : s ≠ R b) : U b s ≠ W b s := by
  intro h
  exact cross_ne hs hne (by rw [← d_mul_U b s, ← d_mul_W b s, h])

theorem H_le_two_S_v {b : ℕ} {s : ℚ} (hb : 0 < b) (hs1 : 1 ≤ s) (hs2 : s ≤ 2) :
    H b s ≤ 2 * S b * v s := by
  apply max_le
  · exact (Nat.div_le_self _ _).trans (by
      have := (S_lt_P_lt_two_S hb).2.le
      exact Nat.mul_le_mul_right (v s) this)
  · exact (Nat.div_le_self _ _).trans (by
      have := Nat.mul_le_mul_left (S b) (u_le_two_v hs1 hs2)
      nlinarith)

end ErdosMahlerAudit.Gate05
