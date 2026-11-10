module

public import ErdosMahlerAudit.Gate06.Multiplicity
public import ErdosMahlerAudit.Gate06.PrescribedProducts
public import ErdosMahlerAudit.Gate06.ProductError

/-! Rational separation forces product transfer, without injectivity or
nonemptiness assumptions, TeX 734–742. -/

public section
namespace ErdosMahlerAudit.Gate06

theorem selected_product_den_le {N b c : ℕ} {ν θ w : ℝ}
    (hb : b ∈ exceptionalBand N ν θ w) (hc : c ∈ exceptionalBand N ν θ w) :
    ((selectedFraction N ν θ w b * selectedFraction N ν θ w c).den : ℝ) ≤ H w ^ 2 :=
  product_den_le_square (selectedFraction_spec hb).2.2 (selectedFraction_spec hc).2.2

theorem prescribed_equality_forces_selected_equality
    {N b c b' c' : ℕ} {ν θ w : ℝ}
    (hθ : 1 < θ) (hθν : θ < ν / 4) (hw : 0 < w)
    (hb : b ∈ exceptionalBand N ν θ w) (hc : c ∈ exceptionalBand N ν θ w)
    (hb' : b' ∈ exceptionalBand N ν θ w) (hc' : c' ∈ exceptionalBand N ν θ w)
    (he : R b * R c = R b' * R c') :
    selectedFraction N ν θ w b * selectedFraction N ν θ w c =
      selectedFraction N ν θ w b' * selectedFraction N ν θ w c' := by
  by_contra hne
  have hsep := bounded_product_separation (H_pos w)
    (selected_product_den_le hb hc) (selected_product_den_le hb' hc') hne
  have herr := equal_prescribed_products_error hb hc hb' hc' he
  exact (not_lt_of_ge hsep) (herr.trans (half_power_gap hθ hθν hw))

/-- A finite quotient comparison. Representatives are chosen only for actual
image members, so the empty case needs no default representative. -/
theorem card_image_le_of_fibers {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (T : Finset α) (f : α → β) (g : α → γ)
    (hf : ∀ x ∈ T, ∀ y ∈ T, f x = f y → g x = g y) :
    (T.image g).card ≤ (T.image f).card := by
  classical
  let rep : (T.image g) → α := fun q => Classical.choose (Finset.mem_image.mp q.property)
  have hrep (q : T.image g) : rep q ∈ T ∧ g (rep q) = q.val :=
    Classical.choose_spec (Finset.mem_image.mp q.property)
  let lift : (T.image g) → (T.image f) := fun q =>
    ⟨f (rep q), Finset.mem_image.mpr ⟨rep q, (hrep q).1, rfl⟩⟩
  apply Finset.card_le_card_of_injective (f := lift)
  intro q r he
  have he' : f (rep q) = f (rep r) := congrArg Subtype.val he
  have hg := hf (rep q) (hrep q).1 (rep r) (hrep r).1 he'
  apply Subtype.ext
  exact (hrep q).2.symm.trans (hg.trans (hrep r).2)

/-- The product transfer itself is valid without a convergent-denominator
hypothesis; that hypothesis is retained by the final manuscript interface. -/
theorem selectedProductSet_card_le_prescribed {N : ℕ} {ν θ w : ℝ}
    (hθ : 1 < θ) (hθν : θ < ν / 4) (hw : 0 < w) :
    (selectedProductSet N ν θ w).card ≤
      (prescribedProductSet (exceptionalBand N ν θ w)).card := by
  rw [selectedProductSet_eq_image]
  apply card_image_le_of_fibers
  intro p hp q hq he
  obtain ⟨hb, hc⟩ := Finset.mem_product.mp hp
  obtain ⟨hb', hc'⟩ := Finset.mem_product.mp hq
  exact prescribed_equality_forces_selected_equality hθ hθν hw hb hc hb' hc' he

/-- Exact Gate 06 product-cardinality contract, with only domain hypotheses. -/
theorem exceptional_product_card_le
    (N : ℕ) (ν θ w : ℝ) (_hN : N ∈ convergentDenominators)
    (_hν4 : 4 < ν) (_hν5 : ν ≤ 5) (hθ1 : 1 < θ) (hθν : θ < ν / 4) (hw : 0 < w) :
    (selectedProductSet N ν θ w).card ≤ 4 * N := by
  apply (selectedProductSet_card_le_prescribed hθ1 hθν hw).trans
  apply prescribedProductSet_card_le
  intro b hb
  exact Finset.mem_Ico.mpr ⟨(mem_exceptionalBand.mp hb).1, (mem_exceptionalBand.mp hb).2.1⟩

end ErdosMahlerAudit.Gate06
