module

public import ErdosMahlerAudit.Gate14.Theorem

/-! Denominator bands of the actual fixed branch (frozen TeX 375–385). -/

@[expose] public section
namespace ErdosMahlerAudit.Gate15
open Filter Gate14

theorem nat_partition {a : ℕ → ℕ} (hm : StrictMono a)
    (hu : Tendsto a atTop atTop) {v : ℕ} (hv : a 0 ≤ v) :
    ∃! j : ℕ, a j ≤ v ∧ v < a (j + 1) := by
  have hex : ∃ n, v < a n := (hu.eventually (eventually_gt_atTop v)).exists
  let n := Nat.find hex
  have hn : v < a n := Nat.find_spec hex
  have hn0 : 0 < n := by
    by_contra h
    have : n = 0 := by omega
    rw [this] at hn
    omega
  have hprev : a (n - 1) ≤ v := Nat.le_of_not_gt (Nat.find_min hex (by omega))
  have hnext : v < a (n - 1 + 1) := by simpa [Nat.sub_add_cancel hn0] using hn
  refine ⟨n - 1, ⟨hprev, hnext⟩, ?_⟩
  intro k hk
  have h1 := hm.lt_iff_lt.mp (hk.1.trans_lt hnext)
  have h2 := hm.lt_iff_lt.mp (hprev.trans_lt hk.2)
  omega

variable {τ : ℝ} {t0 : ℕ} {f : List Bool → ℕ} {ξ : (ℕ → Bool) → ℝ}

theorem denominator_partition (hA : ArithmeticLowerSpec τ t0 f ξ)
    (ε : ℕ → Bool) {v : ℕ} (hv : Q f ε 0 ≤ v) :
    ∃! j : ℕ, Q f ε j ≤ v ∧ v < Q f ε (j + 1) :=
  nat_partition (hA.denominator_strictMono ε) (hA.denominator_tendsto ε) hv

theorem partition_endpoint (hA : ArithmeticLowerSpec τ t0 f ξ)
    (ε : ℕ → Bool) (j k : ℕ) :
    (Q f ε k ≤ Q f ε j ∧ Q f ε j < Q f ε (k + 1)) ↔ k = j := by
  constructor
  · intro h
    have h1 := (hA.denominator_strictMono ε).le_iff_le.mp h.1
    have h2 := (hA.denominator_strictMono ε).lt_iff_lt.mp h.2
    omega
  · intro h
    subst k
    exact ⟨le_rfl, hA.denominator_step ε j⟩

theorem band_index_ge (hA : ArithmeticLowerSpec τ t0 f ξ)
    (ε : ℕ → Bool) {J j v : ℕ} (hJ : Q f ε J ≤ v)
    (hj : v < Q f ε (j + 1)) : J ≤ j := by
  have := (hA.denominator_strictMono ε).lt_iff_lt.mp (hJ.trans_lt hj)
  omega

theorem prescribed_case (hA : ArithmeticLowerSpec τ t0 f ξ)
    (ε : ℕ → Bool) (j : ℕ) {q : ℚ} (hq : q = r f ε j) :
    q.den = Q f ε j ∧ (q.den : ℝ) ^ (-τ) < |ξ ε - (q : ℝ)| := by
  subst q
  rw [hA.denominator]
  exact ⟨rfl, (hA.displacement ε j).1.trans_le (le_abs_self _)⟩

end ErdosMahlerAudit.Gate15
