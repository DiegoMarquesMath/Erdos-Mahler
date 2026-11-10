module

public import ErdosMahlerAudit.Gate11.Successors

/-! One fixed pair per eligible parent, from the actual Gate 11 theorem.
Frozen TeX 319–321. The names left/right refer to bits, not real endpoint order. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate12

noncomputable def width (τ : ℝ) (t : ℕ) : ℝ := Gate11.right τ t - Gate11.left τ t

theorem width_pos (τ : ℝ) (t : ℕ) : 0 < width τ t :=
  sub_pos.mpr (Gate11.left_lt_right τ t)

/-- All properties of one pair, with one shared genuine denominator witness. -/
structure PairSpec (τ : ℝ) (t b c : ℕ) : Prop where
  admissible : ∃ N : ℕ, N ∈ convergentDenominators ∧ 3 ^ t < N ∧
    b ∈ Gate02.admissibleIndices t τ N ∧ c ∈ Gate02.admissibleIndices t τ N
  parent_lt : t < b
  children_lt : b < c
  upper : c < 2 * b
  left_nested : Gate11.K τ b ⊆ interior (Gate11.K τ t)
  right_nested : Gate11.K τ c ⊆ interior (Gate11.K τ t)
  separated : Gate11.right τ b < Gate11.left τ c ∨ Gate11.right τ c < Gate11.left τ b
  disjoint : Disjoint (Gate11.K τ b) (Gate11.K τ c)
  left_decay : width τ b ≤ width τ t / 81 ∧ width τ b < width τ t
  right_decay : width τ c ≤ width τ t / 81 ∧ width τ c < width τ t

/-- Data, not an assumption: `selection_exists` constructs this from Gate 11. -/
structure Selection (τ : ℝ) where
  root : ℕ
  root_pos : 0 < root
  pair : ℕ → ℕ × ℕ
  domain : ∀ t, root ≤ t → Gate11.K τ t ⊆ Set.Ioo 1 2
  valid : ∀ t, root ≤ t → PairSpec τ t (pair t).1 (pair t).2

theorem selection_exists
    (hST : Gate05.SubspaceTwoThreePrimitive) (hMatveev : Gate08.MatveevRationalThree)
    (τ : ℝ) (hτ : 4 ≤ τ) : Nonempty (Selection τ) := by
  classical
  obtain ⟨t0, ht0, hs⟩ := Gate11.nested_disjoint_successor_intervals hST hMatveev τ hτ
  have hp (t : {t : ℕ // t0 ≤ t}) : ∃ p : ℕ × ℕ, PairSpec τ t p.1 p.2 := by
    obtain ⟨N, hN, hNt, b, c, hb, hc, htb, hbc, hc2b, hn, hn', hsep, hd, hw, hw'⟩ :=
      (hs t t.property).2
    exact ⟨(b, c), ⟨⟨N, hN, hNt, hb, hc⟩, htb, hbc, hc2b, hn, hn', hsep, hd, hw, hw'⟩⟩
  let pair (t : ℕ) : ℕ × ℕ :=
    if ht : t0 ≤ t then Classical.choose (hp ⟨t, ht⟩) else (t0, t0)
  refine ⟨⟨t0, ht0, pair, fun t ht => (hs t ht).1, ?_⟩⟩
  intro t ht
  simpa only [pair, dite_eq_left ht] using Classical.choose_spec (hp ⟨t, ht⟩)

noncomputable def selected
    (hST : Gate05.SubspaceTwoThreePrimitive) (hMatveev : Gate08.MatveevRationalThree)
    (τ : ℝ) (hτ : 4 ≤ τ) : Selection τ :=
  Classical.choice (selection_exists hST hMatveev τ hτ)

noncomputable def leftChild
    (hST : Gate05.SubspaceTwoThreePrimitive) (hMatveev : Gate08.MatveevRationalThree)
    (τ : ℝ) (hτ : 4 ≤ τ) (t : ℕ) : ℕ := (selected hST hMatveev τ hτ).pair t |>.1

noncomputable def rightChild
    (hST : Gate05.SubspaceTwoThreePrimitive) (hMatveev : Gate08.MatveevRationalThree)
    (τ : ℝ) (hτ : 4 ≤ τ) (t : ℕ) : ℕ := (selected hST hMatveev τ hτ).pair t |>.2

end ErdosMahlerAudit.Gate12
