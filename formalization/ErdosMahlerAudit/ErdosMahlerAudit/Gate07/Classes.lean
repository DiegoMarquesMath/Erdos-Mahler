module

public import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Group.Torsion
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum

/-! Actual quotient classes and the disjoint-coset injection, TeX 754–774. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate07
open scoped Pointwise
variable {G : Type*} [AddCommGroup G]

/-- Image under scalar dilation, not an iterated sumset. -/
def dilate [DecidableEq G] (q : ℕ) (A : Finset G) : Finset G :=
  A.image (fun a => q • a)

/-- The subgroup qG is the range of the scalar endomorphism. -/
def multipleSubgroup (G : Type*) [AddCommGroup G] (q : ℕ) : AddSubgroup G :=
  (nsmulAddMonoidHom (α := G) q).range

def classMap (q : ℕ) : G →+ G ⧸ multipleSubgroup G q :=
  QuotientAddGroup.mk' (multipleSubgroup G q)

noncomputable def classImage (q : ℕ) (A : Finset G) :
    Finset (G ⧸ multipleSubgroup G q) := by
  classical
  exact A.image (classMap q)

theorem class_eq_iff (q : ℕ) (a b : G) :
    classMap q a = classMap q b ↔ ∃ g : G, a - b = q • g := by
  change (a : G ⧸ multipleSubgroup G q) = b ↔ _
  rw [QuotientAddGroup.eq_iff_sub_mem]
  change (∃ g : G, q • g = a - b) ↔ _
  exact exists_congr fun _ => eq_comm

theorem class_dilate_sub (q : ℕ) (a b : G) :
    classMap q (a - q • b) = classMap q a := by
  apply (class_eq_iff q _ _).mpr
  refine ⟨-b, ?_⟩
  rw [neg_nsmul]
  abel

theorem translated_dilates_disjoint [DecidableEq G] (q : ℕ) (A : Finset G)
    {a b : G} (h : classMap q a ≠ classMap q b) :
    Disjoint (A.image (fun x => a - q • x)) (A.image (fun x => b - q • x)) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨y, _, he⟩ := Finset.mem_image.mp hz'
  apply h
  calc
    classMap q a = classMap q (a - q • x) := (class_dilate_sub q a x).symm
    _ = classMap q (b - q • y) := congrArg (classMap q) he.symm
    _ = classMap q b := class_dilate_sub q b y

theorem dilation_injective [IsAddTorsionFree G] (q : ℕ) (hq : q ≠ 0) :
    Function.Injective (fun a : G => q • a) := by
  intro a b h
  exact eq_of_nsmul_eq_nsmul_of_addCommute hq (show AddCommute a b from add_comm a b) h

theorem dilate_card [DecidableEq G] [IsAddTorsionFree G] (q : ℕ) (hq : q ≠ 0) (A : Finset G) :
    (dilate q A).card = A.card := by
  classical
  exact Finset.card_image_of_injective _ (dilation_injective q hq)

theorem translated_dilate_card [DecidableEq G] [IsAddTorsionFree G]
    (q : ℕ) (hq : q ≠ 0) (a : G) (A : Finset G) :
    (A.image (fun b => a - q • b)).card = A.card := by
  apply Finset.card_image_of_injective
  intro x y he
  exact dilation_injective q hq (sub_right_injective he)

/-- Representatives are chosen only for occupied classes. The map (c,b) ↦ r(c)-qb
is injective: its quotient is c, and then dilation injectivity recovers b. -/
theorem class_card_mul_le [DecidableEq G] [IsAddTorsionFree G]
    (q : ℕ) (hq : q ≠ 0) (A : Finset G) :
    (classImage q A).card * A.card ≤ (A - dilate q A).card := by
  classical
  let C := classImage q A
  let rep : C → G := fun c => Classical.choose (Finset.mem_image.mp c.property)
  have hrep (c : C) : rep c ∈ A ∧ classMap q (rep c) = c.val :=
    Classical.choose_spec (Finset.mem_image.mp c.property)
  let f : C × A → (A - dilate q A) := fun p =>
    ⟨rep p.1 - q • p.2.val, Finset.sub_mem_sub (hrep p.1).1
      (Finset.mem_image.mpr ⟨p.2.val, p.2.property, rfl⟩)⟩
  have hf : Function.Injective f := by
    intro x y he
    have he' : rep x.1 - q • x.2.val = rep y.1 - q • y.2.val := congrArg Subtype.val he
    have hc : x.1 = y.1 := by
      apply Subtype.ext
      calc
        x.1.val = classMap q (rep x.1 - q • x.2.val) :=
          (hrep x.1).2.symm.trans (class_dilate_sub q _ _).symm
        _ = classMap q (rep y.1 - q • y.2.val) := congrArg (classMap q) he'
        _ = y.1.val := (class_dilate_sub q _ _).trans (hrep y.1).2
    have hb : x.2 = y.2 := by
      apply Subtype.ext
      rw [hc] at he'
      exact dilation_injective q hq (sub_right_injective he')
    exact Prod.ext hc hb
  simpa only [Fintype.card_prod, Fintype.card_coe] using Fintype.card_le_of_injective f hf

theorem classImage_empty (q : ℕ) : classImage q (∅ : Finset G) = ∅ := by
  classical
  simp [classImage]

theorem classImage_singleton (q : ℕ) (a : G) : (classImage q {a}).card = 1 := by
  classical
  simp [classImage]

end ErdosMahlerAudit.Gate07
