module

public import ErdosMahlerAudit.Gate07.PositiveRationals

/-! Representatives indexed by distinct selected rationals, TeX 814–815. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate08
open Gate06 Gate07

noncomputable def representative {N : ℕ} {ν θ w : ℝ}
    (s : selectedFractions N ν θ w) : ℕ :=
  Classical.choose (Finset.mem_image.mp s.property)

theorem representative_spec {N : ℕ} {ν θ w : ℝ}
    (s : selectedFractions N ν θ w) :
    representative s ∈ exceptionalBand N ν θ w ∧
      selectedFraction N ν θ w (representative s) = s.val :=
  Classical.choose_spec (Finset.mem_image.mp s.property)

theorem representative_injective (N : ℕ) (ν θ w : ℝ) :
    Function.Injective (representative (N := N) (ν := ν) (θ := θ) (w := w)) := by
  intro s t h
  apply Subtype.ext
  exact (representative_spec s).2.symm.trans
    ((congrArg (selectedFraction N ν θ w) h).trans (representative_spec t).2)

noncomputable def selectedLift {N : ℕ} {ν θ w : ℝ}
    (s : selectedFractions N ν θ w) : PositiveRatAdd :=
  Additive.ofMul ⟨s.val, selectedFractions_positive s.property⟩

theorem selectedLift_value {N : ℕ} {ν θ w : ℝ}
    (s : selectedFractions N ν θ w) : positiveValue (selectedLift s) = s.val := rfl

theorem selectedLift_mem {N : ℕ} {ν θ w : ℝ}
    (s : selectedFractions N ν θ w) : selectedLift s ∈ selectedPositive N ν θ w :=
  Finset.mem_image.mpr ⟨s, Finset.mem_attach _ _, rfl⟩

theorem selected_root {N q : ℕ} {ν θ w : ℝ}
    (s t : selectedFractions N ν θ w) (hne : s ≠ t)
    (hc : classMap q (selectedLift t) = classMap q (selectedLift s)) :
    ∃ g : ℚ, 0 < g ∧ g ≠ 1 ∧ t.val / s.val = g ^ q := by
  obtain ⟨g, hg, he⟩ := (rational_power_class_eq_iff q t.val s.val
    (selectedFractions_positive t.property) (selectedFractions_positive s.property)).mp hc
  refine ⟨g, hg, ?_, he⟩
  intro h
  rw [h, one_pow] at he
  have ht : t.val = s.val := (div_eq_one_iff_eq
    (ne_of_gt (selectedFractions_positive s.property))).mp he
  exact hne (Subtype.ext ht.symm)

/-- The actual fiber in the Gate07 finite set, not a set of band indices. -/
noncomputable def selectedFiber (N : ℕ) (ν θ w : ℝ) (q : ℕ)
    (c : PositiveRatAdd ⧸ multipleSubgroup PositiveRatAdd q) : Finset PositiveRatAdd := by
  classical
  exact (selectedPositive N ν θ w).filter (fun s => classMap q s = c)

theorem selectedFiber_nonempty_iff (N : ℕ) (ν θ w : ℝ) (q : ℕ)
    (c : PositiveRatAdd ⧸ multipleSubgroup PositiveRatAdd q) :
    (selectedFiber N ν θ w q c).Nonempty ↔ c ∈ selectedClasses N ν θ w q := by
  classical
  simp only [selectedFiber, selectedClasses, classImage, Finset.Nonempty, Finset.mem_filter,
    Finset.mem_image]

end ErdosMahlerAudit.Gate08
