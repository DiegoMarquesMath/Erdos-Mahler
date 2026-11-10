module

public import ErdosMahlerAudit.Gate05.Arithmetic

/-! The exact 2,3-smooth part and division-free cancellation, TeX 579–586. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate05

def smoothPart (n : ℕ) : ℕ := 2 ^ n.factorization 2 * 3 ^ n.factorization 3

theorem smoothPart_eq_padicValNat (n : ℕ) :
    smoothPart n = 2 ^ padicValNat 2 n * 3 ^ padicValNat 3 n := by
  simp only [smoothPart, Nat.factorization_def n (by decide : Nat.Prime 2),
    Nat.factorization_def n (by decide : Nat.Prime 3)]

theorem smoothPart_pos (n : ℕ) : 0 < smoothPart n := by unfold smoothPart; positivity

theorem smoothPart_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    smoothPart (m * n) = smoothPart m * smoothPart n := by
  simp only [smoothPart, Nat.factorization_mul hm hn, Finsupp.add_apply, pow_add]
  ring

theorem smoothPart_pow (n k : ℕ) : smoothPart (n ^ k) = smoothPart n ^ k := by
  simp only [smoothPart, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    pow_mul, mul_pow]
  simp only [← pow_mul, Nat.mul_comm]

theorem smoothPart_eq_self {n : ℕ} (hn : n ≠ 0)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ n → p = 2 ∨ p = 3) : smoothPart n = n := by
  apply Nat.eq_of_factorization_eq (smoothPart_pos n).ne' hn
  intro p
  rw [smoothPart, Nat.factorization_mul (by positivity) (by positivity),
    Nat.Prime.factorization_pow (by decide : Nat.Prime 2),
    Nat.Prime.factorization_pow (by decide : Nat.Prime 3), Finsupp.add_apply]
  by_cases h2 : p = 2
  · subst p; simp
  by_cases h3 : p = 3
  · subst p; simp
  have hz : n.factorization p = 0 := by
    by_cases hp : p.Prime
    · apply Nat.factorization_eq_zero_of_not_dvd
      intro hd
      exact (hsupport p hp hd).elim h2 h3
    · exact Nat.factorization_eq_zero_of_not_prime n hp
  simp [h2, h3, hz]

theorem smoothPart_two_pow (k : ℕ) : smoothPart (2 ^ k) = 2 ^ k := by
  apply smoothPart_eq_self (by positivity)
  intro p hp hd
  exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp (hp.dvd_of_dvd_pow hd))

theorem smoothPart_three_pow (k : ℕ) : smoothPart (3 ^ k) = 3 ^ k := by
  apply smoothPart_eq_self (by positivity)
  intro p hp hd
  exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp (hp.dvd_of_dvd_pow hd))

theorem smoothPart_d (b : ℕ) (s : ℚ) : smoothPart (d b s) = d b s :=
  smoothPart_eq_self (d_pos b s).ne' (fun _ hp hd => d_prime_support b s hp hd)

theorem normalized_product (b : ℕ) (s : ℚ) :
    d b s ^ 2 * (U b s * W b s) = P b * S b * (u s * v s) := by
  calc
    _ = (d b s * U b s) * (d b s * W b s) := by ring
    _ = _ := by rw [d_mul_U, d_mul_W]; ring

/-- No natural-number division is used in the conclusion. -/
theorem smoothPart_normalized_product (b : ℕ) {s : ℚ} (hs : 1 ≤ s) :
    d b s ^ 2 * smoothPart (U b s * W b s) =
      P b * S b * smoothPart (u s * v s) := by
  have hd := (d_pos b s).ne'
  have hU := (U_pos b s).ne'
  have hW := (W_pos b hs).ne'
  have hP := (P_pos b).ne'
  have hS := (S_pos b).ne'
  have hu := (u_pos hs).ne'
  have hv := (v_pos s).ne'
  have h := congrArg smoothPart (normalized_product b s)
  rw [smoothPart_mul (pow_ne_zero _ hd) (mul_ne_zero hU hW),
    smoothPart_pow, smoothPart_d,
    smoothPart_mul (mul_ne_zero hP hS) (mul_ne_zero hu hv),
    smoothPart_mul hP hS] at h
  simpa only [P, S, smoothPart_two_pow, smoothPart_three_pow] using h

end ErdosMahlerAudit.Gate05
