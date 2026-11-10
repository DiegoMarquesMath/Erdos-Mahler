module

public import ErdosMahlerAudit.Gate07.Classes
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Rat.Cast.Lemmas

/-! Plünnecke–Ruzsa, triangle iteration, and Lemma 3.4, TeX 776–800. -/

public section
namespace ErdosMahlerAudit.Gate07
open scoped Pointwise
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem dilate_sub (q : ℕ) (A B : Finset G) :
    dilate q (A - B) = dilate q A - dilate q B := by
  ext x
  constructor
  · rintro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hy
    rw [nsmul_sub]
    exact Finset.sub_mem_sub (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
      (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hx
    obtain ⟨u, hu, heu⟩ := Finset.mem_image.mp (show a ∈ A.image (fun x => q • x) from ha)
    obtain ⟨v, hv, hev⟩ := Finset.mem_image.mp (show b ∈ B.image (fun x => q • x) from hb)
    rw [← heu, ← hev]
    exact Finset.mem_image.mpr ⟨u - v, Finset.sub_mem_sub hu hv, nsmul_sub u v q⟩

theorem dilate_mul (q r : ℕ) (A : Finset G) :
    dilate (q * r) A = dilate q (dilate r A) := by
  rw [Nat.mul_comm q r]
  simp only [dilate, Finset.image_image, mul_nsmul, Function.comp_def]

theorem sub_card_swap (A B : Finset G) : (A - B).card = (B - A).card := by
  rw [← Finset.card_neg (A - B), neg_sub]

theorem triple_sub_bound (A : Finset G) (hA : A.Nonempty) :
    ((A - A - A).card : ℝ) ≤ ((A + A).card / (A.card : ℝ)) ^ 3 * A.card := by
  have h := Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add hA A 1 2
  have he : (1 • A - 2 • A) = A - A - A := by
    simp only [one_nsmul, two_nsmul, sub_sub]
  rw [he] at h
  norm_num only [show 1 + 2 = 3 from rfl] at h
  have hh := (NNRat.cast_le (K := ℝ)).mpr h
  push_cast at hh
  exact hh

theorem first_dilate_bound (A : Finset G) (hA : A.Nonempty) :
    ((A - dilate 2 A).card : ℝ) ≤ ((A + A).card / (A.card : ℝ)) ^ 3 * A.card := by
  have hs : A - dilate 2 A ⊆ A - A - A := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hx
    obtain ⟨c, hc, hec⟩ := Finset.mem_image.mp (show b ∈ A.image (fun x => 2 • x) from hb)
    rw [← hec, two_nsmul, ← sub_sub]
    exact Finset.sub_mem_sub (Finset.sub_mem_sub ha hc) hc
  exact (Nat.cast_le.mpr (Finset.card_le_card hs)).trans (triple_sub_bound A hA)

theorem triangle_dilate_step [IsAddTorsionFree G] (A : Finset G)
    (q : ℕ) (hq : q ≠ 0) :
    (A - dilate (q * 2) A).card * A.card ≤
      (A - dilate q A).card * (A - dilate 2 A).card := by
  have h := Finset.ruzsa_triangle_inequality_sub_sub_sub A (dilate q A) (dilate (q * 2) A)
  rw [dilate_card q hq, sub_card_swap (dilate (q * 2) A), dilate_mul,
    ← dilate_sub, dilate_card q hq] at h
  simpa only [dilate_mul] using h

theorem iterated_dilate_bound [IsAddTorsionFree G] (A : Finset G)
    (hA : A.Nonempty) (k : ℕ) (hk : 1 ≤ k) :
    ((A - dilate (2 ^ k) A).card : ℝ) ≤
      ((A + A).card / (A.card : ℝ)) ^ (3 * k) * A.card := by
  have ha : (0 : ℝ) < A.card := Nat.cast_pos.mpr hA.card_pos
  let L : ℝ := (A + A).card / (A.card : ℝ)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  induction k, hk using Nat.le_induction with
  | base => simpa using first_dilate_bound A hA
  | succ k hk ih =>
    have ht : ((A - dilate (2 ^ (k + 1)) A).card : ℝ) * A.card ≤
        (A - dilate (2 ^ k) A).card * (A - dilate 2 A).card := by
      exact_mod_cast (by simpa only [pow_succ] using
        triangle_dilate_step A (2 ^ k) (pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)))
    have hfirst := first_dilate_bound A hA
    have hm := mul_le_mul ih hfirst (Nat.cast_nonneg _) (mul_nonneg (pow_nonneg hL _) ha.le)
    apply (mul_le_mul_iff_left₀ ha).mp
    calc
      _ ≤ _ := ht
      _ ≤ _ := hm
      _ = _ := by
        change (L ^ (3 * k) * A.card) * (L ^ 3 * A.card) =
          (L ^ (3 * (k + 1)) * A.card) * A.card
        rw [Nat.mul_add, Nat.mul_one, pow_add]
        ring

/-- Lemma 3.4: exact quotient, coefficient one, exponent 3*k. -/
theorem power_class_bound [IsAddTorsionFree G] (A : Finset G)
    (hA : A.Nonempty) (k : ℕ) (hk : 1 ≤ k) :
    ((classImage (2 ^ k) A).card : ℝ) ≤
      ((A + A).card / (A.card : ℝ)) ^ (3 * k) := by
  have ha : (0 : ℝ) < A.card := Nat.cast_pos.mpr hA.card_pos
  apply (mul_le_mul_iff_left₀ ha).mp
  calc
    _ ≤ ((A - dilate (2 ^ k) A).card : ℝ) := by
      exact_mod_cast class_card_mul_le (2 ^ k) (pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)) A
    _ ≤ _ := iterated_dilate_bound A hA k hk

end ErdosMahlerAudit.Gate07
