module

public import ErdosMahlerAudit.Gate06.Band

/-! Counting actual prescribed products through two ceiling values, TeX 705–717. -/

public section
namespace ErdosMahlerAudit.Gate06

theorem prescribed_product_formula (b c : ℕ) :
    R b * R c = (2 : ℚ) ^ (a b + a c) / (3 : ℚ) ^ (b + c) := by
  simp only [R, pow_add, div_mul_div_comm]

/-- Includes zero indices; no appeal to a strict ceiling gap at zero. -/
theorem ceiling_sum_two_values (b c : ℕ) :
    a b + a c = a (b + c) ∨ a b + a c = a (b + c) + 1 := by
  have hlo : a (b + c) ≤ a b + a c := by
    simpa only [a, Nat.cast_add, add_mul] using
      Nat.ceil_add_le ((b : ℝ) * alpha) ((c : ℝ) * alpha)
  have hb := Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg b) alpha_pos.le)
  have hc := Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg c) alpha_pos.le)
  have hl : ((b + c : ℕ) : ℝ) * alpha ≤ (a (b + c) : ℝ) := Nat.le_ceil _
  have hhi : (a b : ℝ) + (a c : ℝ) < (a (b + c) : ℝ) + 2 := by
    dsimp [a] at *
    push_cast at hl ⊢
    linarith
  have hhi' : a b + a c < a (b + c) + 2 := by exact_mod_cast hhi
  omega

theorem index_sum_mem {N b c : ℕ}
    (hb : b ∈ Finset.Ico N (2 * N)) (hc : c ∈ Finset.Ico N (2 * N)) :
    b + c ∈ Finset.Ico (2 * N) (4 * N) := by
  simp only [Finset.mem_Ico] at *
  omega

/-- A finite containing image, not a count of index pairs. -/
theorem prescribedProductSet_card_le {N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Ico N (2 * N)) :
    (prescribedProductSet A).card ≤ 4 * N := by
  classical
  let grid := (Finset.Ico (2 * N) (4 * N)).product (Finset.range 2)
  let f : ℕ × ℕ → ℚ := fun p => (2 : ℚ) ^ (a p.1 + p.2) / (3 : ℚ) ^ p.1
  have hsub : prescribedProductSet A ⊆ grid.image f := by
    intro q hq
    obtain ⟨⟨b, c⟩, hbc, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hb, hc⟩ := Finset.mem_product.mp hbc
    have hl := index_sum_mem (hA hb) (hA hc)
    rcases ceiling_sum_two_values b c with he | he
    · refine Finset.mem_image.mpr ⟨(b + c, 0), Finset.mem_product.mpr ⟨hl, by simp⟩, ?_⟩
      simp only [f, prescribed_product_formula, he, Nat.add_zero]
    · refine Finset.mem_image.mpr ⟨(b + c, 1), Finset.mem_product.mpr ⟨hl, by simp⟩, ?_⟩
      simp only [f, prescribed_product_formula, he]
  calc
    _ ≤ (grid.image f).card := Finset.card_le_card hsub
    _ ≤ grid.card := Finset.card_image_le
    _ = 4 * N := by
      change ((Finset.Ico (2 * N) (4 * N)) ×ˢ (Finset.range 2)).card = 4 * N
      rw [Finset.card_product, Nat.card_Ico, Finset.card_range]
      omega

end ErdosMahlerAudit.Gate06
