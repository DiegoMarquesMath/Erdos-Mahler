module

public import ErdosMahlerAudit.Gate04.Neighborhood
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Prod

/-! Exact band and chosen canonical rational witnesses, TeX 656–677. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate06

noncomputable def V (θ w : ℝ) : ℝ := Real.exp (w / θ)
noncomputable def H (w : ℝ) : ℝ := Real.exp w

noncomputable def exceptionalBand (N : ℕ) (ν θ w : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Ico N (2 * N)).filter (fun b => ∃ s : ℚ,
    Exceptional b ν s ∧ max (V θ w) ((N : ℝ) ^ (1 / 3 : ℝ)) < (s.den : ℝ) ∧
      (s.den : ℝ) ≤ H w)

theorem mem_exceptionalBand {N b : ℕ} {ν θ w : ℝ} :
    b ∈ exceptionalBand N ν θ w ↔ N ≤ b ∧ b < 2 * N ∧ ∃ s : ℚ,
      Exceptional b ν s ∧ max (V θ w) ((N : ℝ) ^ (1 / 3 : ℝ)) < (s.den : ℝ) ∧
        (s.den : ℝ) ≤ H w := by
  classical
  simp [exceptionalBand, and_assoc]

/-- The fallback is outside the band only and is never included in X. -/
noncomputable def selectedFraction (N : ℕ) (ν θ w : ℝ) (b : ℕ) : ℚ :=
  if hb : b ∈ exceptionalBand N ν θ w then
    Classical.choose (mem_exceptionalBand.mp hb).2.2 else 0

theorem selectedFraction_spec {N b : ℕ} {ν θ w : ℝ}
    (hb : b ∈ exceptionalBand N ν θ w) :
    Exceptional b ν (selectedFraction N ν θ w b) ∧
      max (V θ w) ((N : ℝ) ^ (1 / 3 : ℝ)) <
        ((selectedFraction N ν θ w b).den : ℝ) ∧
      ((selectedFraction N ν θ w b).den : ℝ) ≤ H w := by
  classical
  simpa only [selectedFraction, dite_eq_left hb] using
    Classical.choose_spec (mem_exceptionalBand.mp hb).2.2

noncomputable def selectedFractions (N : ℕ) (ν θ w : ℝ) : Finset ℚ :=
  (exceptionalBand N ν θ w).image (selectedFraction N ν θ w)

noncomputable def selectedProductSet (N : ℕ) (ν θ w : ℝ) : Finset ℚ :=
  ((selectedFractions N ν θ w).product (selectedFractions N ν θ w)).image
    (fun p => p.1 * p.2)

noncomputable def prescribedProductSet (A : Finset ℕ) : Finset ℚ :=
  (A.product A).image (fun p => R p.1 * R p.2)

theorem selectedProductSet_eq_image (N : ℕ) (ν θ w : ℝ) :
    selectedProductSet N ν θ w =
      ((exceptionalBand N ν θ w).product (exceptionalBand N ν θ w)).image
        (fun p => selectedFraction N ν θ w p.1 * selectedFraction N ν θ w p.2) := by
  ext q
  constructor
  · intro hq
    obtain ⟨⟨x, y⟩, hxy, heq⟩ := Finset.mem_image.mp hq
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨(b, c), Finset.mem_product.mpr ⟨hb, hc⟩, heq⟩
  · intro hq
    obtain ⟨⟨b, c⟩, hbc, heq⟩ := Finset.mem_image.mp hq
    obtain ⟨hb, hc⟩ := Finset.mem_product.mp hbc
    exact Finset.mem_image.mpr ⟨(_, _), Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨b, hb, rfl⟩, Finset.mem_image.mpr ⟨c, hc, rfl⟩⟩, heq⟩

theorem selectedFractions_positive {N : ℕ} {ν θ w : ℝ} {s : ℚ}
    (hs : s ∈ selectedFractions N ν θ w) : 0 < s := by
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hs
  exact lt_of_lt_of_le (by norm_num) (selectedFraction_spec hb).1.2.2.2.1

theorem selected_sets_empty {N : ℕ} {ν θ w : ℝ}
    (h : exceptionalBand N ν θ w = ∅) :
    selectedFractions N ν θ w = ∅ ∧ selectedProductSet N ν θ w = ∅ := by
  simp [selectedFractions, selectedProductSet, h]

end ErdosMahlerAudit.Gate06
