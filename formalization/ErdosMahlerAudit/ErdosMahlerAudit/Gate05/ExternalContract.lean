module

public import ErdosMahlerAudit.Gate05.LocalProduct

/-! Schlickewei, printed p. 246, (1.3)–(1.5), specialized to determinant-one
forms (X-Y,Y) at infinity and (X,Y) at 2 and 3. This is a proposition to be
passed explicitly, not a proof of the published external theorem. -/

@[expose] public section
namespace ErdosMahlerAudit.Gate05

def SubspaceTwoThreePrimitive : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 →
    Set.Finite {z : ℕ × ℕ | 0 < z.1 ∧ 0 < z.2 ∧ Nat.Coprime z.1 z.2 ∧
      localProduct z.1 z.2 < ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) ^ (-δ / 2)}

end ErdosMahlerAudit.Gate05
