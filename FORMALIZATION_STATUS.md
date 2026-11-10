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
| Gate 06 | Products of exceptional fractions (Lemma 3.3): exact finite rational witnesses, multiplicity `|A(w)| ≤ 4|X|`, and product bound `|XX| ≤ 4N`; 31 additional theorems and 7 definitions | None for the two finite product inequalities |
| Gate 07 | Classes modulo rational powers (Lemma 3.4): abstract bound `#(A mod 2^k G) ≤ (|A+A|/|A|)^(3k)` and actual positive-rational bound `#classes(X) ≤ (4N/|X|)^(3k)`; 33 proved theorems, 7 definitions, 2 type abbreviations | None for the final class-count theorems |
| Gate 08 | Size of a class (Lemma 3.5): ratio rigidity, exact index gap, and `#(X ∩ class) ≤ 13w` for the least `2^k ≥ log(N/w)^2`; 50 theorems, 11 definitions | `Gate08.MatveevRationalThree`, an explicitly typed weighted 3-logarithm theorem not proved in Lean |
| Gate 09 | Count in a denominator range (Lemma 3.6): actual band satisfies `#A(w)/N ≤ 16 exp(−x/(52 log(2+x)))`, `x=log(N/w)` above a common absolute threshold; 13 theorems | Only the explicit `Gate08.MatveevRationalThree` parameter inherited from Gate 08 |
| Gate 10 | Global summation, tail control, Proposition 2.1 with absolute `C=60` and actual two-successor corollary; 33 proved theorems and 3 transparent definitions | Exactly `Gate05.SubspaceTwoThreePrimitive` and `Gate08.MatveevRationalThree` as explicit undischarged ordinary parameters |
| Gate 11 | Real closed intervals `K τ t`, ordered admissible successors, strict nesting and disjointness, rational separation, and width contraction by at least a factor of `81`; 23 declarations in the reported local audit | Exactly the same two explicit external parameters; no independent repository CI yet |
| Gate 12 | One globally coherent `List Bool → ℕ` tree; actual selected admissible successor pairs, sibling disjointness, nested closed intervals, growth of indices, uniform interval-width bound `width(root)/81^depth`; 14 proved theorems, 5 definitions, 3 transparent structures (76 namespace declarations audited locally) | Same two ordinary external parameters; no independent repository CI yet |
| Gate 13 | Unique limit for every infinite binary branch; continuity, injectivity, compact/closed/perfect nowhere-dense image homeomorphic to binary Cantor space; every prescribed rational satisfies strict displacement at every depth; 49 handwritten definitions/theorems and 1 structure (77 namespace declarations audited locally) | Same two ordinary external parameters; no independent repository CI yet |
| Gate 14 | Irrationality of every Cantor branch limit via rational separation; actual reduced prescribed fractions are genuine regular continued-fraction convergents of the branch limit via the pinned mathlib Legendre criterion; increasing denominators, infinitude, and eventual approximation for every real `0<s<τ`; 68 new namespace declarations audited locally | Same two ordinary external parameters; upper exponent bound and numeric supremum definition not yet proved |
| Gate 15 | Unique natural-denominator partition, small/large/prescribed rational comparison, inherited admissibility at the next index, uniform all-canonical-rational lower bound for each exponent gap, and finiteness of too-good rational approximation sets; 29 handwritten theorems and 57 namespace declarations audited locally | Same two ordinary external parameters; numeric supremum exponent definition and final assembly not yet proved |
| Gate 16 | Genuine `ENNReal` supremum of orders with infinite canonical-rational approximation sets, unconditional order-theoretic upper/lower bridges, and final `Gate16.erdos_mahler_main` constructing a Cantor image with exact exponent and infinitely many actual prescribed regular convergents; 14 new declarations audited | Exactly the two inherited undischarged ordinary external mathematical premises; no independent repository CI |

**Gate 03 removes the rotation and unboundedness hypotheses from the successor theorem.** In the local development, the central declaration is

```lean
ErdosMahlerAudit.Gate03.counting_implies_successors
```

It has the exact counting proposition as an **explicit theorem argument**. It does not assume the existence of admissible successors. Its conclusion gives two distinct admissible indices arbitrarily far out for each sufficiently large parent, including $\tau=4$.

The specialized open-real-interval rotation bound, sufficient for the intervals actually used in the construction, was locally established with discrepancy at most $6$. Gate 04 further establishes the exact small-denominator inequality, using the same rotation machinery for arbitrary rational-witness neighborhoods. The controlling constant is $60$, independent of the exponent and cutoffs. The manuscript's more general statement for arbitrary arcs in $\mathbb R/\mathbb Z$ has not been formalized in full.

Gate 05 verifies the deduction of the following statements from the ordinary parameter `hST : Gate05.SubspaceTwoThreePrimitive`: for each $\varepsilon>0$, all sufficiently large indices and all reduced rational witnesses in $[1,2]$ satisfy $|R(b)-u/v|\ge 3^{-\varepsilon b}v^{-2}$; for each fixed $4<\nu\le5$, the exact finite-maximum logarithmic height $W_N(\nu)$ satisfies $W_N(\nu)/N\to0$ along $\mathcal D$. The external primitive-pair finiteness proposition is **not proved in Lean**. The reported proof of $W_N=0$ means that every exceptional witness has denominator $1$, not that no exceptional witness exists. In particular, `Exceptional 5 5 1` is checked.

Gate 06 establishes the two exact finite-set inequalities `|A(w)| ≤ 4|X|` and `|XX| ≤ 4N` without an external mathematical premise. Rational-product separation and the ceiling two-value restriction are verified in its supporting modules. This result does not establish the Matveev estimate or the final counting proposition.

Gate 07 proves the exact quotient by `2^k` multiples, distinguishes finite-set dilation from iterated sumsets, and uses the pinned Mathlib Plünnecke–Ruzsa and Ruzsa triangle inequalities. The associated positive-rational quotient is the actual group `ℚ_{>0}^×`, and the finite-set specialization uses Gate 06's selected fractions and product estimate, rather than an assumed product bound. This is an unconditional local deduction at the lemma's scope. The next local deduction is the combination of class-count and class-size bounds.

Gate 08 proves a class-size bound with the explicit absolute constant `13` and an absolute threshold of the form `100(C₀+1)`, where the constant `C₀` comes from the exact **weighted** Matveev contract. The hypothesis `MatveevRationalThree` is an ordinary, undischarged theorem parameter. The real-height and 3-adic valuation bridges, minimum power `q=2^k≥x²`, and injective choice of representatives are part of the checked local derivation. Neither this external theorem nor the separate Gate 05 Subspace Theorem has been formally established.

Gate 09 proves the one-band estimate from the actual finite exceptional set with explicit constants `c=1/52` and `C=16`, above the threshold `100(C₀+1)`. The proof includes the empty-set case, the exact exponent `3k+1`, and the necessary logarithmic comparison. Gate 10 then proves the global summation using a genuinely summable majorant, the exact half-open height partition, eventually large active indices from Gate 05 and the finite-set tail Cauchy criterion. The resulting Proposition 2.1 has **one absolute coefficient `C=60` fixed before all exponent, denominator and tolerance parameters**. The optional `Gate10.two_successors` corollary supplies the two distinct admissible indices for each sufficiently large parent, including `τ=4`. These are **local conditional proofs** under the two identified external results, not a verification of the main theorem or a GitHub CI certificate. Gate 11 additionally reports `Gate11.nested_disjoint_successor_intervals` for all real `τ ≥ 4`. It derives ordered successors from `Gate10.two_successors`, proves strict inclusion of both child intervals in the parent, their disjointness, and width contraction. The reported local `lake build` (7,230 jobs) and direct `Gate11Checks.lean` both exited successfully, with only standard kernel axioms in the 23 declarations. The two published-mathematics contracts remain explicit ordinary arguments. These results are based on local log output, not a remote source build.

These claims are grounded in the submitted local verification reports and theorem-type output. **The proof source files are not yet present in this remote repository and these builds have not been independently reproduced on GitHub.**

## Remaining mathematical work

| Target | Current status |
| --- | --- |
| Full all-arcs version of the rotation estimate | Open; specialized interval theorem completed locally |
| Small-exceptional-denominator counting (Lemma 3.1; Gate 04) | **Verified locally** — exact theorem with `C = 60`; repository CI pending |
| Sublinear height bound from the $p$-adic Subspace Theorem (Gate 05) | **Verified locally, conditional** on the explicit external contract; remote CI pending |
| Product-transfer and product-cardinality arguments (Gate 06) | **Verified locally** — both final inequalities; repository CI pending |
| Classes modulo rational powers (Lemma 3.4; Gate 07) | **Verified locally** — abstract and concrete rational-power bounds; repository CI pending |
| Matveev and size of power classes (Lemma 3.5; Gate 08) | **Verified locally, conditional** on `MatveevRationalThree`; repository CI pending |
| Single-band large-denominator count (Lemma 3.6; Gate 09) | **Verified locally, conditional** on weighted Matveev; repository CI pending |
| Summation over logarithmic denominator ranges (Gate 10) | **Verified locally, conditional** on the two explicit external results; repository CI pending |
| Proposition 2.1 with one absolute constant | **Verified locally, conditional**; exact `Gate10.proposition_2_1` has `C=60` chosen before `ν,D,η` |
| Nested intervals and disjoint successors (Gate 11) | **Verified locally, conditional** — exact geometric bridges from `Gate10.two_successors`; GitHub CI pending |
| Coherent binary interval tree (Gate 12) | **Verified locally, conditional** — one fixed selector and root; interval widths at depth `n` at most `width(root)/81^n` |
| Infinite-chain limits, Cantor embedding, compactness and perfectness (Gate 13) | **Verified locally, conditional** — one actual tree, continuous injective branch map, compact perfect nowhere-dense image, strict displacement |
| Irrationality and infinitely many regular convergents (Gate 14) | **Verified locally, conditional** — genuine `Real.convergent`, strictly increasing powers-of-three denominators, all orders below `τ` |
| Uniform upper irrationality-exponent bound (Gate 15) | **Verified locally, conditional** — all reduced rationals, denominator-bound threshold for every branch and exponent gap, finite too-good sets |

| Standard numeric exponent bridge and full theorem (Gate 16) | **Verified locally, conditional** — final `Gate16.erdos_mahler_main` with exactly two explicit external premises |
| Exact irrationality exponent and infinitely many prescribed regular convergents | **Verified locally, conditional**; proof depends on Gate 05 and Gate 08 contracts |

External published inputs (including Subspace Theorem, weighted Matveev and Plünnecke–Ruzsa) must be checked against their precise hypotheses. If they are not imported from verified formal libraries or proved in Lean, they must remain plainly visible as assumptions.

## Reproducibility and source identity

The local reports specify:

- Lean toolchain: `leanprover/lean4:v4.36.0-rc2`.
- mathlib revision: `9d581dfff2e41de989072ea63abf3daf69311520`.
- Gate 03: `lake build` completed (4,478 jobs); `Gate03Checks.lean` completed without errors.
- Gate 04: `lake build` completed (4,492 jobs); `Gate04Checks.lean` completed without errors. The final theorem `Gate04.small_denominator_absolute` has no additional mathematical hypotheses and provides `C=60`.
- Gate 05: `lake build` completed (4,520 jobs); `Gate05Checks.lean` completed without errors. Its main quantitative theorems depend on the ordinary, explicitly typed parameter `SubspaceTwoThreePrimitive`, not on a newly declared axiom.
- Gate 06: `lake build` completed (4,534 jobs); `Gate06Checks.lean` completed without errors. The final product and multiplicity theorems have no external mathematical hypotheses.
- Gate 07: after `lake clean ErdosMahlerAudit`, `lake build` completed (4,548 jobs); `Gate07Checks.lean` completed without errors. Both the abstract theorem `Gate07.power_class_bound` and its concrete positive-rational corollary `Gate07.selected_fractions_power_class_bound` have no new mathematical hypotheses.
- Gate 08: `lake build` completed (7,196 jobs); `Gate08Checks.lean` completed without errors. Three final theorems `Gate08.same_class_ratio_rigidity`, `Gate08.same_class_index_gap`, and `Gate08.selected_class_card_le` were checked under the explicit ordinary Matveev parameter. No clean-build claim is made for this incremental build.
- Gate 09: `lake build` completed (7,204 jobs); `Gate09Checks.lean` completed without errors. The final `Gate09.denominator_range_bound` retains the one visible ordinary parameter `MatveevRationalThree`. This was an incremental local build.
- Gate 10: `lake build` completed (7,222 jobs); `Gate10Checks.lean` completed without errors. The results `Gate10.large_denominator_negligible`, `Gate10.proposition_2_1` and `Gate10.two_successors` were checked in the local report. Their types retain exactly the two undischarged ordinary parameters `SubspaceTwoThreePrimitive` and `MatveevRationalThree`.
- Gate 11: reported `lake build` completed (7,230 jobs) and direct `Gate11Checks.lean` exited 0. The 23 new declarations passed the recorded stored-body and axiom audits. This is a local conditional result, not a remote or full-main-theorem certificate. The interrupted Gate 11 preflight required a new operational integrity baseline; that replacement does not retrospectively certify byte identity with the original Gate 10 compilation.
- Gate 12: reported `lake build` completed (7,236 jobs) and direct `Gate12Checks.lean` exited 0. The final declaration `Gate12.binary_tree_of_intervals` has only the two inherited mathematical premises and the bound `4 ≤ τ`; the constructed `TreeSpec` contains real interval nesting and disjointness, actual admissible successors, and depth-wise contraction. The local audit reports 76 Gate 12 namespace declarations checked for unwanted axioms, and an operational Gate 11→12 snapshot preserving all existing sources except the authorized appended root import. This has not been independently reproduced from committed Lean sources.
- Gate 13: reported `lake build` completed (7,244 jobs) and direct `Gate13Checks.lean` exited 0. The final `Gate13.cantor_set_of_tau` has exactly the two inherited mathematical premises plus `τ` and `4 ≤ τ`; the resulting `CantorSpec` proves unique branch limits, continuity, injectivity, compactness, closedness, no isolated points, homeomorphism with binary sequence space, empty interior, nowhere density, and exact strict displacement for every depth. The local audit reports 77 Gate 13 namespace declarations and 518 transitively reachable project declarations inspected for hidden axioms or opaque bodies. This is not a GitHub CI certificate.
- Gate 14: reported `lake build` completed (7,256 jobs) and `Gate14Checks.lean` exited 0. The public `Gate14.prescribed_convergents_lower_exponent` retains exactly the two inherited ordinary external mathematical premises and `4 ≤ τ`. Its `ArithmeticLowerSpec` proves actual `Irrational`, `Real.convergent` and `GenContFract.of` membership, distinct prescribed reduced fractions, and infinitely many rational approximants at every exponent strictly below `τ`. The local audit reports 68 Gate 14 namespace declarations, 65 stored bodies and a 562-declaration transitive project traversal. This is not independent CI, and no numeric `μ` statement is claimed.
- Gate 15: reported `lake build` completed (7,268 jobs) and direct `Gate15Checks.lean` exited 0. The public `Gate15.upper_irrationality_exponent` takes exactly the two inherited mathematical premises and `4 ≤ τ`, retaining the same `K, ξ, t0, f`, `CantorSpec` and `ArithmeticLowerSpec`. Its transparent `UpperSpec` proves high-denominator lower bounds over **all** canonical rationals and finiteness of each too-good approximation set of real order `s>τ`. The local audit reports 57 namespace declarations, 54 stored bodies and 665 transitively reachable project declarations inspected. This is not independent repository CI; no numeric `μ` equality is claimed.
- Gate 16: reported `lake build` completed (7,274 jobs) and direct `Gate16Checks.lean` exited 0. The public `Gate16.erdos_mahler_main` has exactly the two inherited external propositions as ordinary premises, followed by `τ : ℝ` and `4 ≤ τ`. Its full conclusion retains one `CantorSpec`, one `ArithmeticLowerSpec`, one `UpperSpec`, and proves `irrationalityExponent x = ENNReal.ofReal τ` with infinitely many distinct actual regular convergents having canonical numerator `2^A` and denominator `3^B` for every point in the Cantor image. The local report audits 14 new stored mathematical declarations and 682 transitively reachable project declarations. This is a **conditional local proof**, not a remote build, a source audit of earlier gates, or a proof of either external proposition.
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

The full implication from `Gate05.SubspaceTwoThreePrimitive` and `Gate08.MatveevRationalThree` to the integrated main theorem is reported **locally kernel-checked through Gate 16**. Unconditional certification remains open until the two exact mathematical contracts are justified or formalized. No independent GitHub CI build has yet run against published Lean sources; those source files remain absent from the remote repository.
