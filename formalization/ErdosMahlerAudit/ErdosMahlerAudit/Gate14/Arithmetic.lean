module

public import ErdosMahlerAudit.Gate13.Topology
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Actual prescribed fractions along a fixed inherited tree. Frozen TeX 326–367. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate14
open Filter
open scoped Topology

def t (f : List Bool → ℕ) (ε : ℕ → Bool) (n : ℕ) : ℕ := f (Gate13.«prefix» ε n)
def Q (f : List Bool → ℕ) (ε : ℕ → Bool) (n : ℕ) : ℕ := 3 ^ t f ε n
noncomputable def r (f : List Bool → ℕ) (ε : ℕ → Bool) (n : ℕ) : ℚ := R (t f ε n)

variable {τ : ℝ} {t0 : ℕ} {f : List Bool → ℕ} {ξ : (ℕ → Bool) → ℝ} {K : Set ℝ}

@[simp] theorem r_num (ε : ℕ → Bool) (n : ℕ) :
    (r f ε n).num = (2 : ℤ) ^ a (t f ε n) := R_num _
@[simp] theorem r_den (ε : ℕ → Bool) (n : ℕ) : (r f ε n).den = Q f ε n := R_den _
theorem r_reduced (ε : ℕ → Bool) (n : ℕ) :
    Nat.Coprime (2 ^ a (t f ε n)) (Q f ε n) := R_coprime _
theorem r_eq (ε : ℕ → Bool) (n : ℕ) :
    r f ε n = (2 : ℚ) ^ a (t f ε n) / (Q f ε n : ℚ) := by simp [r, R, Q]
theorem Q_pos (ε : ℕ → Bool) (n : ℕ) : 0 < Q f ε n := by unfold Q; positivity

theorem radius_eq (ε : ℕ → Bool) (n : ℕ) :
    (3 : ℝ) ^ (-τ * (t f ε n : ℝ)) = (Q f ε n : ℝ) ^ (-τ) := by
  simpa only [Gate02.radius, Q, Nat.cast_pow, Nat.cast_ofNat] using Gate02.radius_eq_Q (t f ε n) τ

variable (hC : Gate13.CantorSpec τ t0 f ξ K)
include hC

theorem t_zero (ε : ℕ → Bool) : t f ε 0 = t0 := by simp [t, hC.tree.root_eq]
theorem t_height (ε : ℕ → Bool) (n : ℕ) : t0 + n ≤ t f ε n :=
  Gate13.branch_height hC.tree ε n

theorem t_pos (ε : ℕ → Bool) (n : ℕ) : 0 < t f ε n :=
  hC.tree.root_pos.trans_le (hC.tree.lower _)

theorem t_step (ε : ℕ → Bool) (n : ℕ) : t f ε n < t f ε (n + 1) := by
  dsimp only [t]
  rw [Gate13.prefix_succ]
  have hp := hC.tree.pairs (Gate13.«prefix» ε n)
  cases h : ε n with
  | false => exact hp.parent_lt
  | true => exact hp.parent_lt.trans hp.children_lt

theorem t_strictMono (ε : ℕ → Bool) : StrictMono (t f ε) :=
  strictMono_nat_of_lt_succ (t_step hC ε)

theorem Q_three_le (ε : ℕ → Bool) (n : ℕ) : 3 ≤ Q f ε n := by
  have h := pow_le_pow_right₀ (by decide : 1 ≤ (3 : ℕ)) (t_pos hC ε n)
  simpa [Q] using h

theorem Q_strictMono (ε : ℕ → Bool) : StrictMono (Q f ε) := by
  intro m n hmn
  exact pow_lt_pow_right₀ (by decide : 1 < (3 : ℕ)) (t_strictMono hC ε hmn)

theorem Q_step (ε : ℕ → Bool) (n : ℕ) : Q f ε n < Q f ε (n + 1) :=
  Q_strictMono hC ε (Nat.lt_succ_self n)

theorem Q_triple (ε : ℕ → Bool) (n : ℕ) : 3 * Q f ε n ≤ Q f ε (n + 1) := by
  have h := pow_le_pow_right₀ (by decide : 1 ≤ (3 : ℕ)) (t_step hC ε n)
  simpa [Q, pow_succ, mul_comm] using h

theorem Q_tendsto (ε : ℕ → Bool) : Tendsto (Q f ε) atTop atTop :=
  (Q_strictMono hC ε).tendsto_atTop

theorem Q_real_tendsto (ε : ℕ → Bool) :
    Tendsto (fun n => (Q f ε n : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (Q_tendsto hC ε)

theorem r_injective (ε : ℕ → Bool) : Function.Injective (r f ε) := by
  intro m n h
  exact (Q_strictMono hC ε).injective (by simpa only [r_den] using congrArg Rat.den h)

theorem r_range_infinite (ε : ℕ → Bool) : (Set.range (r f ε)).Infinite :=
  Set.infinite_range_of_injective (r_injective hC ε)

theorem displacement (ε : ℕ → Bool) (n : ℕ) :
    (Q f ε n : ℝ) ^ (-τ) < ξ ε - (r f ε n : ℝ) ∧
    ξ ε - (r f ε n : ℝ) < 3 * (Q f ε n : ℝ) ^ (-τ) := by
  simpa only [← radius_eq, t, r] using hC.displacement ε n

theorem displacement_pos (ε : ℕ → Bool) (n : ℕ) : 0 < ξ ε - (r f ε n : ℝ) :=
  (Real.rpow_pos_of_pos (by exact_mod_cast Q_pos ε n) _).trans (displacement hC ε n).1

end ErdosMahlerAudit.Gate14
