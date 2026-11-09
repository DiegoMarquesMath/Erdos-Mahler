# Formalization status

This document records the correspondence between the current manuscript and the Lean 4 development. It distinguishes kernel-checked deductions, conditional proofs, and results still outside the formalization. It will be updated as new sources and reproducible builds become available.

## Statements under verification

The underlying objects are

$$
\alpha=\frac{\log3}{\log2},\quad
R(b)=\frac{2^{\lceil b\alpha\rceil}}{3^b},
\quad \mathcal D=\{\text{convergent denominators of }\alpha\}.
$$

For $4<\nu\le5$, the exceptional count $E_N(D,\nu)$ concerns reduced fractions $u/v\in[1,2]$, distinct from $R(b)$, satisfying $v>D$ and $|R(b)-u/v|<1/(16v^\nu)$. The quantitative target is

$$
\exists C>0\quad\forall\nu\in(4,5]\quad\forall D\ge2:\qquad
\limsup_{\substack{N\to\infty\\N\in\mathcal D}}
\frac{E_N(D,\nu)}N\le CD^{2-\nu}.
$$

The main theorem states the existence, for each $\tau\ge4$, of a Cantor set of irrationality exponent exactly $\tau$ with infinitely many regular convergents of the form $2^a/3^b$.

## Established locally

| Stage | Verified statements reported by the local Lean build | Dependencies not discharged by that stage |
| --- | --- | --- |
| Gate 01 | Exact definitions, reduced numerators and denominators, rational separation, foundational arithmetic; 29 theorem declarations | None for the recorded elementary theorems |
| Gate 02 | Exact finite index sets, admissibility, density bounds, and the two-successor deduction; 28 additional theorems | Counting estimate; rotation discrepancy; unbounded convergent denominators for actual successor selection |
| Gate 03 | Unboundedness of actual convergent denominators, approximation by convergents, open-interval discrepancy with constant 6, and successors; 26 additional theorems | Counting estimate for the final successor theorem |
| Gate 04 | Small-denominator estimate (Lemma 3.1), with an explicit absolute constant `C = 60`; 37 additional theorems and 9 definitions | None for Lemma 3.1 |
| Gate 05 | Canonical arithmetic normalization, local product, height lower bound, and fixed-exponent logarithmic escape; 66 additional theorems and 15 definitions | The precise finite-primitive-pairs consequence `SubspaceTwoThreePrimitive` of the p-adic Subspace Theorem is an explicit, undischarged theorem parameter |

**Gate 03 removes the rotation and unboundedness hypotheses from the successor theorem.** In the local development, the central declaration is

```lean
ErdosMahlerAudit.Gate03.counting_implies_successors
```

It has the exact counting proposition as an **explicit theorem argument**. It does not assume the existence of admissible successors. Its conclusion gives two distinct admissible indices arbitrarily far out for each sufficiently large parent, including $\tau=4$.

The specialized open-real-interval rotation bound, sufficient for the intervals actually used in the construction, was locally established with discrepancy at most $6$. Gate 04 further establishes the exact small-denominator inequality, using the same rotation machinery for arbitrary rational-witness neighborhoods. The controlling constant is $60$, independent of the exponent and cutoffs. The manuscript's more general statement for arbitrary arcs in $\mathbb R/\mathbb Z$ has not been formalized in full.

Gate 05 verifies the deduction of the following statements from the ordinary parameter `hST : Gate05.SubspaceTwoThreePrimitive`: for each $\varepsilon>0$, all sufficiently large indices and all reduced rational witnesses in $[1,2]$ satisfy $|R(b)-u/v|\ge 3^{-\varepsilon b}v^{-2}$; for each fixed $4<\nu\le5$, the exact finite-maximum logarithmic height $W_N(\nu)$ satisfies $W_N(\nu)/N\to0$ along $\mathcal D$. The external primitive-pair finiteness proposition is **not proved in Lean**. The reported proof of $W_N=0$ means that every exceptional witness has denominator $1$, not that no exceptional witness exists. In particular, `Exceptional 5 5 1` is checked.

These claims are grounded in the submitted local verification reports and theorem-type output. **The proof source files are not yet present in this remote repository and these builds have not been independently reproduced on GitHub.**

## Remaining mathematical work

| Target | Current status |
| --- | --- |
| Full all-arcs version of the rotation estimate | Open; specialized interval theorem completed locally |
| Small-exceptional-denominator counting (Lemma 3.1; Gate 04) | **Verified locally** — exact theorem with `C = 60`; repository CI pending |
| Sublinear height bound from the $p$-adic Subspace Theorem (Gate 05) | **Verified locally, conditional** on the explicit external contract; remote CI pending |
| Product-transfer and product-cardinality arguments (Gate 06) | In progress; no local verified theorem yet |
| Rational-power classes, Matveev, and combinatorial bounds | Not yet formalized |
| Summation over logarithmic denominator ranges | Not yet formalized |
| Proposition 2.1 with one absolute constant | Not yet formalized |
| Nested intervals, Cantor embedding and $\mu(\xi)=\tau$ | Not yet formalized |

External published inputs (including Subspace Theorem, weighted Matveev and Plünnecke–Ruzsa) must be checked against their precise hypotheses. If they are not imported from verified formal libraries or proved in Lean, they must remain plainly visible as assumptions.

## Reproducibility and source identity

The local reports specify:

- Lean toolchain: `leanprover/lean4:v4.36.0-rc2`.
- mathlib revision: `9d581dfff2e41de989072ea63abf3daf69311520`.
- Gate 03: `lake build` completed (4,478 jobs); `Gate03Checks.lean` completed without errors.
- Gate 04: `lake build` completed (4,492 jobs); `Gate04Checks.lean` completed without errors. The final theorem `Gate04.small_denominator_absolute` has no additional mathematical hypotheses and provides `C=60`.
- Gate 05: `lake build` completed (4,520 jobs); `Gate05Checks.lean` completed without errors. Its main quantitative theorems depend on the ordinary, explicitly typed parameter `SubspaceTwoThreePrimitive`, not on a newly declared axiom.
- Only the usual kernel axiom dependencies `propext`, `Classical.choice`, and `Quot.sound` were reported for the new theorem declarations.

Frozen manuscript hashes (recorded from the local project, pending repository reproduction):

```text
Erdos_Mahler.tex  5a55f32babc285ed9ad05fcb3bd6f8fe2bd3080d9eca7fd11e79ba23f7307116
Erdos_Mahler.pdf  9d9558f33236b6c1d7b276876153bf3d87f6fac2019c6e39db4d988e5022927f
```

The source tree will be published under `formalization/ErdosMahlerAudit/`, retaining its own `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`. Only after its GitHub build succeeds will individual rows be designated as **Verified in CI**.

## Verification standards

1. Every claimed conclusion must match the elaborated theorem type and the actual manuscript statement.
2. No `sorry`, `admit`, `sorryAx`, custom axiom, or unchecked surrogate statement may be used to close a mathematical obligation.
3. Review `#check @...` and `#print axioms`. The absence of new axioms alone is insufficient: inspect ordinary theorem parameters as well.
4. Check the pinned dependencies and source-file hashes before finalizing any release.
5. Keep conditional proofs visibly conditional, and distinguish local evidence from independent repository reproduction.

A complete formal certification of Proposition 2.1 and of the counterexample theorem is **not yet claimed**.
