module

public import ErdosMahlerAudit.Gate12.Tree
public import Mathlib.Data.List.OfFn
public import Mathlib.Topology.MetricSpace.PiNat

/-! Ordered prefixes of the actual Gate 12 tree; the product topology is unchanged. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate13

def «prefix» (ε : ℕ → Bool) (n : ℕ) : List Bool := List.ofFn (fun i : Fin n => ε i)

@[simp] theorem prefix_zero (ε : ℕ → Bool) : «prefix» ε 0 = [] := rfl

theorem prefix_succ (ε : ℕ → Bool) (n : ℕ) :
    «prefix» ε (n + 1) = «prefix» ε n ++ [ε n] := by
  exact List.ofFn_succ_last

@[simp] theorem prefix_length (ε : ℕ → Bool) (n : ℕ) : («prefix» ε n).length = n := by
  simp [«prefix»]

theorem prefix_eq_iff (ε η : ℕ → Bool) (n : ℕ) :
    «prefix» ε n = «prefix» η n ↔ ∀ i < n, ε i = η i := by
  rw [«prefix», «prefix», List.ofFn_inj]
  constructor
  · intro h i hi
    exact congrFun h ⟨i, hi⟩
  · intro h
    funext i
    exact h i i.isLt

theorem first_divergence {ε η : ℕ → Bool} (h : ε ≠ η) :
    ∃ n, «prefix» ε n = «prefix» η n ∧ ε n ≠ η n := by
  refine ⟨PiNat.firstDiff ε η, (prefix_eq_iff _ _ _).2 ?_, PiNat.apply_firstDiff_ne h⟩
  intro i hi
  exact PiNat.apply_eq_of_lt_firstDiff hi

theorem prefix_cylinder (ε : ℕ → Bool) (n : ℕ) :
    {η | «prefix» η n = «prefix» ε n} = PiNat.cylinder ε n := by
  ext η
  exact prefix_eq_iff η ε n

theorem isOpen_prefix (ε : ℕ → Bool) (n : ℕ) :
    IsOpen {η | «prefix» η n = «prefix» ε n} := by
  rw [prefix_cylinder]
  exact PiNat.isOpen_cylinder (fun _ => Bool) ε n

def flip (ε : ℕ → Bool) (n : ℕ) : ℕ → Bool :=
  fun i => if i = n then !(ε i) else ε i

theorem flip_ne (ε : ℕ → Bool) (n : ℕ) : flip ε n ≠ ε := by
  intro h
  have hi := congrFun h n
  simp [flip] at hi

theorem prefix_flip (ε : ℕ → Bool) (n : ℕ) : «prefix» (flip ε n) n = «prefix» ε n := by
  apply (prefix_eq_iff _ _ _).2
  intro i hi
  simp [flip, Nat.ne_of_lt hi]

end ErdosMahlerAudit.Gate13
