module

public import ErdosMahlerAudit.Gate13.Limits
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Homeomorph.Lemmas

/-! The image of the unique-limit map of one actual Gate 12 tree. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate13
open Filter
open scoped Topology

variable {τ : ℝ} {t0 : ℕ} {f : List Bool → ℕ} (hTree : Gate12.TreeSpec τ t0 f)

theorem point_continuous : Continuous (point hTree) := by
  apply Metric.continuous_iff'.2
  intro ε δ hδ
  obtain ⟨n, hn⟩ := width_bound_small τ t0 hδ
  have hc : {η | «prefix» η n = «prefix» ε n} ∈ 𝓝 ε :=
    (isOpen_prefix ε n).mem_nhds rfl
  filter_upwards [hc] with η hη
  rw [Real.dist_eq]
  exact (point_prefix_bound hTree η ε n hη).trans_lt hn

theorem point_injective : Function.Injective (point hTree) := by
  intro ε η heq
  by_contra hne
  obtain ⟨n, hp, hd⟩ := first_divergence hne
  have hε := point_mem hTree ε (n + 1)
  have hη := point_mem hTree η (n + 1)
  dsimp only [interval] at hε hη
  rw [prefix_succ] at hε hη
  rw [← hp, ← heq] at hη
  have hdis := (hTree.pairs («prefix» ε n)).disjoint
  cases hεn : ε n <;> cases hηn : η n
  · exact hd (hεn.trans hηn.symm)
  · rw [hεn] at hε
    rw [hηn] at hη
    exact Set.disjoint_left.mp hdis hε hη
  · rw [hεn] at hε
    rw [hηn] at hη
    exact Set.disjoint_left.mp hdis hη hε
  · exact hd (hεn.trans hηn.symm)

noncomputable def cantorImage : Set ℝ := Set.range (point hTree)

theorem image_nonempty : (cantorImage hTree).Nonempty :=
  ⟨point hTree (fun _ => false), ⟨fun _ => false, rfl⟩⟩

theorem image_subset : cantorImage hTree ⊆ Set.Ioo 1 2 := by
  rintro x ⟨ε, rfl⟩
  exact hTree.domain («prefix» ε 0) (point_mem hTree ε 0)

theorem image_compact : IsCompact (cantorImage hTree) :=
  isCompact_range (point_continuous hTree)

theorem image_closed : IsClosed (cantorImage hTree) := (image_compact hTree).isClosed

noncomputable def image_homeomorph : (ℕ → Bool) ≃ₜ cantorImage hTree :=
  ((point_continuous hTree).isClosedEmbedding (point_injective hTree)).isEmbedding.toHomeomorph

theorem image_homeomorph_coe (ε : ℕ → Bool) :
    (image_homeomorph hTree ε : ℝ) = point hTree ε := rfl

theorem image_no_isolated (x : ℝ) (hx : x ∈ cantorImage hTree) (δ : ℝ) (hδ : 0 < δ) :
    ∃ y ∈ cantorImage hTree, y ≠ x ∧ |y - x| < δ := by
  obtain ⟨ε, rfl⟩ := hx
  obtain ⟨n, hn⟩ := width_bound_small τ t0 hδ
  refine ⟨point hTree (flip ε n), ⟨flip ε n, rfl⟩, ?_, ?_⟩
  · exact fun h => flip_ne ε n (point_injective hTree h)
  · exact (point_prefix_bound hTree (flip ε n) ε n (prefix_flip ε n)).trans_lt hn

theorem image_totallyDisconnected : IsTotallyDisconnected (cantorImage hTree) := by
  have he := ((point_continuous hTree).isClosedEmbedding (point_injective hTree)).isEmbedding
  exact he.isTotallyDisconnected_range.mpr inferInstance

theorem image_interior_empty : interior (cantorImage hTree) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨δ, hδ, hb⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  have hs : Set.Icc x (x + δ / 2) ⊆ cantorImage hTree := by
    intro y hy
    apply interior_subset (hb ?_)
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hy.1)]
    linarith [hy.2]
  have hle : x ≤ x + δ / 2 := by linarith
  have heq := image_totallyDisconnected hTree _ hs isPreconnected_Icc
    (Set.left_mem_Icc.mpr hle) (Set.right_mem_Icc.mpr hle)
  linarith

theorem image_closure_interior_empty : interior (closure (cantorImage hTree)) = ∅ := by
  rw [(image_closed hTree).closure_eq, image_interior_empty hTree]

/-- All conclusions concern one tree and one map, including its actual range subtype. -/
structure CantorSpec (τ : ℝ) (t0 : ℕ) (f : List Bool → ℕ)
    (ξ : (ℕ → Bool) → ℝ) (K : Set ℝ) : Prop where
  tree : Gate12.TreeSpec τ t0 f
  range_eq : K = Set.range ξ
  nonempty : K.Nonempty
  subset : K ⊆ Set.Ioo 1 2
  continuous : Continuous ξ
  injective : Function.Injective ξ
  compact : IsCompact K
  closed : IsClosed K
  no_isolated : ∀ x ∈ K, ∀ δ : ℝ, 0 < δ → ∃ y ∈ K, y ≠ x ∧ |y - x| < δ
  homeomorph : ∃ e : (ℕ → Bool) ≃ₜ K, ∀ ε, (e ε : ℝ) = ξ ε
  interior_empty : interior K = ∅
  nowhere_dense : interior (closure K) = ∅
  unique : ∀ ε, ∃! x : ℝ, ∀ n, x ∈ Gate11.K τ (f («prefix» ε n))
  mem : ∀ ε n, ξ ε ∈ Gate11.K τ (f («prefix» ε n))
  interior_mem : ∀ ε n, ξ ε ∈ interior (Gate11.K τ (f («prefix» ε n)))
  displacement : ∀ ε n,
    (3 : ℝ) ^ (-τ * (f («prefix» ε n) : ℝ)) < ξ ε - (R (f («prefix» ε n)) : ℝ) ∧
    ξ ε - (R (f («prefix» ε n)) : ℝ) < 3 * (3 : ℝ) ^ (-τ * (f («prefix» ε n) : ℝ))
  prefix_bound : ∀ ε η n, «prefix» ε n = «prefix» η n →
    |ξ ε - ξ η| ≤ Gate12.width τ t0 / (81 : ℝ) ^ n

theorem cantor_set_from_tree :
    CantorSpec τ t0 f (point hTree) (cantorImage hTree) where
  tree := hTree
  range_eq := rfl
  nonempty := image_nonempty hTree
  subset := image_subset hTree
  continuous := point_continuous hTree
  injective := point_injective hTree
  compact := image_compact hTree
  closed := image_closed hTree
  no_isolated := image_no_isolated hTree
  homeomorph := ⟨image_homeomorph hTree, image_homeomorph_coe hTree⟩
  interior_empty := image_interior_empty hTree
  nowhere_dense := image_closure_interior_empty hTree
  unique := unique_limit hTree
  mem := point_mem hTree
  interior_mem := point_interior hTree
  displacement := point_displacement hTree
  prefix_bound := point_prefix_bound hTree

/-- The tree is obtained once, outside all branch and depth quantifiers. -/
theorem cantor_set_of_tau
    (hST : Gate05.SubspaceTwoThreePrimitive) (hMatveev : Gate08.MatveevRationalThree)
    (τ : ℝ) (hτ : 4 ≤ τ) :
    ∃ (K : Set ℝ) (ξ : (ℕ → Bool) → ℝ) (t0 : ℕ) (f : List Bool → ℕ),
      CantorSpec τ t0 f ξ K := by
  obtain ⟨t0, f, hTree⟩ := Gate12.binary_tree_of_intervals hST hMatveev τ hτ
  exact ⟨cantorImage hTree, point hTree, t0, f, cantor_set_from_tree hTree⟩

end ErdosMahlerAudit.Gate13
