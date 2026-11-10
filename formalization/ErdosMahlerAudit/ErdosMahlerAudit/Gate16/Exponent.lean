module

public import ErdosMahlerAudit.Gate15.Theorem
public import Mathlib.Basic.ENNReal.Real

/-! The numeric exponent uses all positive real orders and distinct canonical rationals. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate16

/-- Canonical denominators include one; positive error excludes the exact value. -/
def Good (x : ℝ) (s : ℝ) : Set ℚ :=
  {q : ℚ | 0 < |x - (q : ℝ)| ∧ |x - (q : ℝ)| < (q.den : ℝ) ^ (-s)}

/-- Positivity of the order is imposed separately in the numeric supremum. -/
def ApproxOrder (x s : ℝ) : Prop := (Good x s).Infinite

/-- A global extended numeric value, with no imposed finite bound or attainment. -/
noncomputable def irrationalityExponent (x : ℝ) : ENNReal :=
  sSup {z : ENNReal | ∃ s : ℝ, 0 < s ∧ ApproxOrder x s ∧ z = ENNReal.ofReal s}

theorem mem_good (x s : ℝ) (q : ℚ) :
    q ∈ Good x s ↔ 0 < |x - (q : ℝ)| ∧ |x - (q : ℝ)| < (q.den : ℝ) ^ (-s) :=
  Iff.rfl

theorem exponent_eq_sSup (x : ℝ) : irrationalityExponent x =
    sSup {z : ENNReal | ∃ s : ℝ, 0 < s ∧ (Good x s).Infinite ∧
      z = ENNReal.ofReal s} := rfl

theorem ofReal_le_exponent {x s : ℝ} (hs : 0 < s) (h : ApproxOrder x s) :
    ENNReal.ofReal s ≤ irrationalityExponent x :=
  le_sSup ⟨s, hs, h, rfl⟩

theorem exponent_le {x : ℝ} {b : ENNReal}
    (h : ∀ s : ℝ, 0 < s → ApproxOrder x s → ENNReal.ofReal s ≤ b) :
    irrationalityExponent x ≤ b := by
  apply sSup_le
  rintro z ⟨s, hs, ha, rfl⟩
  exact h s hs ha

/-- No finiteness assumption at the endpoint is needed. -/
theorem exponent_le_of_finite {x τ : ℝ} (_hτ : 0 < τ)
    (h : ∀ s : ℝ, τ < s → (Good x s).Finite) :
    irrationalityExponent x ≤ ENNReal.ofReal τ := by
  apply exponent_le
  intro s _ hs
  apply ENNReal.ofReal_le_ofReal
  by_contra! hlt
  exact hs.not_finite (h s hlt)

/-- If the supremum is finite and below τ, density supplies a positive real order
strictly between its real value and τ, contradicting the supremum bound. -/
theorem ofReal_le_exponent_of_infinite {x τ : ℝ} (_hτ : 0 < τ)
    (h : ∀ s : ℝ, 0 < s → s < τ → (Good x s).Infinite) :
    ENNReal.ofReal τ ≤ irrationalityExponent x := by
  by_cases htop : irrationalityExponent x = ⊤
  · rw [htop]
    exact le_top
  · apply (ENNReal.ofReal_le_iff_le_toReal htop).2
    by_contra! hlt
    obtain ⟨s, hμs, hsτ⟩ := exists_between hlt
    have hs : 0 < s := lt_of_le_of_lt ENNReal.toReal_nonneg hμs
    have hb := ofReal_le_exponent hs (h s hs hsτ)
    exact (not_le_of_gt hμs) ((ENNReal.ofReal_le_iff_le_toReal htop).1 hb)

/-- Unbounded approximation orders really give the infinite extended value. -/
theorem exponent_eq_top_of_all_orders {x : ℝ}
    (h : ∀ s : ℝ, 0 < s → (Good x s).Infinite) :
    irrationalityExponent x = ⊤ := by
  by_contra htop
  have hs : 0 < (irrationalityExponent x).toReal + 1 := by
    have := ENNReal.toReal_nonneg (a := irrationalityExponent x)
    linarith
  have hb := ofReal_le_exponent hs (h _ hs)
  have := (ENNReal.ofReal_le_iff_le_toReal htop).1 hb
  linarith

end ErdosMahlerAudit.Gate16
