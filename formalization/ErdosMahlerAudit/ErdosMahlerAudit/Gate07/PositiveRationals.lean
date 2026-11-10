module

public import ErdosMahlerAudit.Gate07.Growth
public import ErdosMahlerAudit.Gate06.ProductTransfer
public import Mathlib.Algebra.Order.Positive.Field
public import Mathlib.Algebra.Group.TypeTags.Basic

/-! The actual positive rational group, and the Gate 06 specialization. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate07
open scoped Pointwise

/-- Exactly the positive rationals; in particular -1 is not an element. -/
abbrev PositiveRat := {r : ℚ // 0 < r}

/-- Additive notation for multiplication of positive rationals. -/
abbrev PositiveRatAdd := Additive PositiveRat

def positiveValue (a : PositiveRatAdd) : ℚ := a.toMul.val

theorem positiveValue_injective : Function.Injective positiveValue := by
  intro a b h
  exact Subtype.ext h

theorem positiveValue_pos (a : PositiveRatAdd) : 0 < positiveValue a := a.toMul.property

theorem positiveValue_add (a b : PositiveRatAdd) :
    positiveValue (a + b) = positiveValue a * positiveValue b := rfl

theorem positiveValue_sub (a b : PositiveRatAdd) :
    positiveValue (a - b) = positiveValue a / positiveValue b := by
  simp [positiveValue, div_eq_mul_inv]

theorem positiveValue_nsmul (q : ℕ) (a : PositiveRatAdd) :
    positiveValue (q • a) = positiveValue a ^ q := rfl

/-- The group has no torsion, as follows from its ordered positive group structure. -/
theorem positiveRatAdd_torsionFree : IsAddTorsionFree PositiveRatAdd := inferInstance

/-- This is an equivalence about actual rational values, with a positive rational root.
The consistently chosen orientation is s/t. -/
theorem positive_class_eq_iff (q : ℕ) (s t : PositiveRatAdd) :
    classMap q s = classMap q t ↔
      ∃ g : ℚ, 0 < g ∧ positiveValue s / positiveValue t = g ^ q := by
  rw [class_eq_iff]
  constructor
  · rintro ⟨g, h⟩
    refine ⟨positiveValue g, positiveValue_pos g, ?_⟩
    simpa only [positiveValue_sub, positiveValue_nsmul] using congrArg positiveValue h
  · rintro ⟨g, hg, he⟩
    refine ⟨Additive.ofMul (⟨g, hg⟩ : PositiveRat), ?_⟩
    apply positiveValue_injective
    rw [positiveValue_sub, positiveValue_nsmul]
    exact he

theorem rational_power_class_eq_iff (q : ℕ) (s t : ℚ) (hs : 0 < s) (ht : 0 < t) :
    classMap q (Additive.ofMul (⟨s, hs⟩ : PositiveRat)) =
      classMap q (Additive.ofMul (⟨t, ht⟩ : PositiveRat)) ↔
      ∃ g : ℚ, 0 < g ∧ s / t = g ^ q :=
  positive_class_eq_iff q _ _

/-- Proof-carrying lift of exactly the selected rational witnesses, without a fallback value. -/
noncomputable def selectedPositive (N : ℕ) (ν θ w : ℝ) : Finset PositiveRatAdd :=
  (Gate06.selectedFractions N ν θ w).attach.image
    (fun s => Additive.ofMul (⟨s.val, Gate06.selectedFractions_positive s.property⟩ : PositiveRat))

theorem selectedPositive_value_image (N : ℕ) (ν θ w : ℝ) :
    (selectedPositive N ν θ w).image positiveValue = Gate06.selectedFractions N ν θ w := by
  ext s
  simp [selectedPositive, Finset.image_image, positiveValue]

theorem selectedPositive_card (N : ℕ) (ν θ w : ℝ) :
    (selectedPositive N ν θ w).card = (Gate06.selectedFractions N ν θ w).card := by
  rw [← selectedPositive_value_image N ν θ w,
    Finset.card_image_of_injective _ positiveValue_injective]

theorem selectedPositive_sum_image (N : ℕ) (ν θ w : ℝ) :
    (selectedPositive N ν θ w + selectedPositive N ν θ w).image positiveValue =
      Gate06.selectedProductSet N ν θ w := by
  let A := selectedPositive N ν θ w
  have hv := selectedPositive_value_image N ν θ w
  change (A + A).image positiveValue = _
  ext z
  constructor
  · intro hz
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hc
    apply Finset.mem_image.mpr
    refine ⟨(positiveValue a, positiveValue b), Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · rw [← hv]; exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    · rw [← hv]; exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
    · exact (positiveValue_add a b).symm
  · intro hz
    obtain ⟨⟨a, b⟩, hab, he⟩ := Finset.mem_image.mp hz
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    rw [← hv] at ha hb
    obtain ⟨s, hs, hes⟩ := Finset.mem_image.mp ha
    obtain ⟨t, ht, het⟩ := Finset.mem_image.mp hb
    exact Finset.mem_image.mpr ⟨s + t, Finset.add_mem_add hs ht,
      (positiveValue_add s t).trans (by simpa only [hes, het] using he)⟩

theorem selectedPositive_sum_card (N : ℕ) (ν θ w : ℝ) :
    (selectedPositive N ν θ w + selectedPositive N ν θ w).card =
      (Gate06.selectedProductSet N ν θ w).card := by
  rw [← selectedPositive_sum_image N ν θ w,
    Finset.card_image_of_injective _ positiveValue_injective]

noncomputable def selectedClasses (N : ℕ) (ν θ w : ℝ) (q : ℕ) :
    Finset (PositiveRatAdd ⧸ multipleSubgroup PositiveRatAdd q) :=
  classImage q (selectedPositive N ν θ w)

/-- Membership explicitly identifies the occupied classes with the original X. -/
theorem mem_selectedClasses (N : ℕ) (ν θ w : ℝ) (q : ℕ)
    (c : PositiveRatAdd ⧸ multipleSubgroup PositiveRatAdd q) :
    c ∈ selectedClasses N ν θ w q ↔ ∃ s : PositiveRatAdd,
      positiveValue s ∈ Gate06.selectedFractions N ν θ w ∧ classMap q s = c := by
  classical
  have hv := selectedPositive_value_image N ν θ w
  constructor
  · intro hc
    obtain ⟨s, hs, he⟩ := Finset.mem_image.mp hc
    exact ⟨s, hv ▸ Finset.mem_image.mpr ⟨s, hs, rfl⟩, he⟩
  · rintro ⟨s, hs, he⟩
    rw [← hv] at hs
    obtain ⟨t, ht, hts⟩ := Finset.mem_image.mp hs
    have hts' := positiveValue_injective hts
    subst t
    exact Finset.mem_image.mpr ⟨s, ht, he⟩

theorem selectedClasses_empty {N : ℕ} {ν θ w : ℝ}
    (hX : Gate06.selectedFractions N ν θ w = ∅) (q : ℕ) :
    selectedClasses N ν θ w q = ∅ := by
  classical
  simp [selectedClasses, selectedPositive, hX, classImage]

/-- Exact nonempty specialization, including the intermediate actual product ratio. -/
theorem selected_fractions_power_class_bounds
    (N : ℕ) (ν θ w : ℝ) (hN : N ∈ convergentDenominators)
    (hν4 : 4 < ν) (hν5 : ν ≤ 5) (hθ1 : 1 < θ) (hθν : θ < ν / 4) (hw : 0 < w)
    (hM : 0 < (Gate06.selectedFractions N ν θ w).card) (k : ℕ) (hk : 1 ≤ k) :
    ((selectedClasses N ν θ w (2 ^ k)).card : ℝ) ≤
      ((Gate06.selectedProductSet N ν θ w).card /
        ((Gate06.selectedFractions N ν θ w).card : ℝ)) ^ (3 * k) ∧
    ((Gate06.selectedProductSet N ν θ w).card /
        ((Gate06.selectedFractions N ν θ w).card : ℝ)) ^ (3 * k) ≤
      (4 * (N : ℝ) / (Gate06.selectedFractions N ν θ w).card) ^ (3 * k) := by
  have hA : (selectedPositive N ν θ w).Nonempty := by
    apply Finset.card_pos.mp
    rwa [selectedPositive_card]
  have hb := power_class_bound (selectedPositive N ν θ w) hA k hk
  rw [selectedPositive_card, selectedPositive_sum_card] at hb
  refine ⟨hb, ?_⟩
  have hp : ((Gate06.selectedProductSet N ν θ w).card : ℝ) ≤ 4 * (N : ℝ) := by
    exact_mod_cast Gate06.exceptional_product_card_le N ν θ w hN hν4 hν5 hθ1 hθν hw
  have hm : (0 : ℝ) < (Gate06.selectedFractions N ν θ w).card := Nat.cast_pos.mpr hM
  exact pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hp hm.le) _

/-- Final Gate 06 corollary, with the product estimate discharged internally. -/
theorem selected_fractions_power_class_bound
    (N : ℕ) (ν θ w : ℝ) (hN : N ∈ convergentDenominators)
    (hν4 : 4 < ν) (hν5 : ν ≤ 5) (hθ1 : 1 < θ) (hθν : θ < ν / 4) (hw : 0 < w)
    (hM : 0 < (Gate06.selectedFractions N ν θ w).card) (k : ℕ) (hk : 1 ≤ k) :
    ((selectedClasses N ν θ w (2 ^ k)).card : ℝ) ≤
      (4 * (N : ℝ) / (Gate06.selectedFractions N ν θ w).card) ^ (3 * k) := by
  have h := selected_fractions_power_class_bounds N ν θ w hN hν4 hν5 hθ1 hθν hw hM k hk
  exact h.1.trans h.2

end ErdosMahlerAudit.Gate07
