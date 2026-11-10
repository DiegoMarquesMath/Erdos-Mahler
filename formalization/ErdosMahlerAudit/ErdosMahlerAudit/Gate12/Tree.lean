module

public import ErdosMahlerAudit.Gate12.Selection

/-! Coherent finite words and exact geometric decay (frozen TeX 319–331).
No infinite paths or limit points are asserted here. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate12

variable (hST : Gate05.SubspaceTwoThreePrimitive) (hMatveev : Gate08.MatveevRationalThree)
  (τ : ℝ) (hτ : 4 ≤ τ)

noncomputable def node (w : List Bool) : ℕ :=
  w.foldl (fun t bit => if bit then rightChild hST hMatveev τ hτ t
    else leftChild hST hMatveev τ hτ t) (selected hST hMatveev τ hτ).root

theorem node_nil : node hST hMatveev τ hτ [] = (selected hST hMatveev τ hτ).root := rfl

theorem node_append (w : List Bool) (bit : Bool) :
    node hST hMatveev τ hτ (w ++ [bit]) =
      if bit then rightChild hST hMatveev τ hτ (node hST hMatveev τ hτ w)
      else leftChild hST hMatveev τ hτ (node hST hMatveev τ hτ w) := by
  simp [node, List.foldl_append]

theorem node_false (w : List Bool) :
    node hST hMatveev τ hτ (w ++ [false]) =
      leftChild hST hMatveev τ hτ (node hST hMatveev τ hτ w) := by
  simp [node_append]

theorem node_true (w : List Bool) :
    node hST hMatveev τ hτ (w ++ [true]) =
      rightChild hST hMatveev τ hτ (node hST hMatveev τ hτ w) := by
  simp [node_append]

theorem node_height (w : List Bool) :
    (selected hST hMatveev τ hτ).root + w.length ≤ node hST hMatveev τ hτ w := by
  induction w using List.reverseRecOn with
  | nil => simp [node_nil]
  | append_singleton w bit ih =>
    have ht : (selected hST hMatveev τ hτ).root ≤ node hST hMatveev τ hτ w := by omega
    have hp := (selected hST hMatveev τ hτ).valid _ ht
    have hl : node hST hMatveev τ hτ w <
        leftChild hST hMatveev τ hτ (node hST hMatveev τ hτ w) := hp.parent_lt
    have hr : node hST hMatveev τ hτ w <
        rightChild hST hMatveev τ hτ (node hST hMatveev τ hτ w) :=
      hp.parent_lt.trans hp.children_lt
    rw [node_append]
    cases bit <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_append,
      List.length_singleton] <;> omega

theorem root_le_node (w : List Bool) :
    (selected hST hMatveev τ hτ).root ≤ node hST hMatveev τ hτ w := by
  have := node_height hST hMatveev τ hτ w
  omega

theorem node_pair (w : List Bool) :
    PairSpec τ (node hST hMatveev τ hτ w)
      (node hST hMatveev τ hτ (w ++ [false]))
      (node hST hMatveev τ hτ (w ++ [true])) := by
  rw [node_false, node_true]
  exact (selected hST hMatveev τ hτ).valid _ (root_le_node hST hMatveev τ hτ w)

theorem node_domain (w : List Bool) :
    Gate11.K τ (node hST hMatveev τ hτ w) ⊆ Set.Ioo 1 2 :=
  (selected hST hMatveev τ hτ).domain _ (root_le_node hST hMatveev τ hτ w)

theorem node_step (w : List Bool) (bit : Bool) :
    node hST hMatveev τ hτ w < node hST hMatveev τ hτ (w ++ [bit]) ∧
    width τ (node hST hMatveev τ hτ (w ++ [bit])) ≤
      width τ (node hST hMatveev τ hτ w) / 81 := by
  have hp := node_pair hST hMatveev τ hτ w
  cases bit with
  | false => exact ⟨hp.parent_lt, hp.left_decay.1⟩
  | true => exact ⟨hp.parent_lt.trans hp.children_lt, hp.right_decay.1⟩

/-- The divisor is positive at every finite depth, including depth zero. -/
theorem decay_denominator_pos (n : ℕ) : (0 : ℝ) < 81 ^ n := by positivity

theorem node_width_bound (w : List Bool) :
    width τ (node hST hMatveev τ hτ w) ≤
      width τ (selected hST hMatveev τ hτ).root / (81 : ℝ) ^ w.length := by
  induction w using List.reverseRecOn with
  | nil => simp [node_nil]
  | append_singleton w bit ih =>
    have h81 : (0 : ℝ) < 81 := by norm_num
    calc
      width τ (node hST hMatveev τ hτ (w ++ [bit])) ≤
          width τ (node hST hMatveev τ hτ w) / 81 :=
        (node_step hST hMatveev τ hτ w bit).2
      _ ≤ (width τ (selected hST hMatveev τ hτ).root / 81 ^ w.length) / 81 :=
        div_le_div_of_nonneg_right ih h81.le
      _ = width τ (selected hST hMatveev τ hτ).root / 81 ^ (w ++ [bit]).length := by
        rw [List.length_append, List.length_singleton, pow_succ, div_div]

/-- Transparent finite-tree conclusion. The tree is a conclusion of the public theorem. -/
structure TreeSpec (τ : ℝ) (t0 : ℕ) (f : List Bool → ℕ) : Prop where
  root_pos : 0 < t0
  root_eq : f [] = t0
  lower : ∀ w, t0 ≤ f w
  height : ∀ w, t0 + w.length ≤ f w
  pairs : ∀ w, PairSpec τ (f w) (f (w ++ [false])) (f (w ++ [true]))
  domain : ∀ w, Gate11.K τ (f w) ⊆ Set.Ioo 1 2
  positive : ∀ w, 0 < width τ (f w)
  decay : ∀ w, width τ (f w) ≤ width τ t0 / (81 : ℝ) ^ w.length

include hST hMatveev hτ in
/-- Gate 12: only the two inherited external contracts are mathematical inputs. -/
theorem binary_tree_of_intervals :
    ∃ t0 : ℕ, ∃ f : List Bool → ℕ, TreeSpec τ t0 f := by
  refine ⟨(selected hST hMatveev τ hτ).root, node hST hMatveev τ hτ, ?_⟩
  exact ⟨(selected hST hMatveev τ hτ).root_pos, node_nil hST hMatveev τ hτ,
    root_le_node hST hMatveev τ hτ, node_height hST hMatveev τ hτ,
    node_pair hST hMatveev τ hτ, node_domain hST hMatveev τ hτ,
    fun w => width_pos τ _, node_width_bound hST hMatveev τ hτ⟩

end ErdosMahlerAudit.Gate12
