# Erdős–Mahler

**Formal verification of *A counterexample to the Erdős–Mahler conjecture***  
Diego Marques · Universidade de Brasília

This repository accompanies the manuscript *A counterexample to the Erdős–Mahler conjecture*. Its purpose is to provide a reproducible Lean 4 formalization of the main mathematical arguments, with exact theorem statements, explicit dependencies, and an independently checkable record of progress.

## Mathematical result

The manuscript proves that for every real number $\tau\ge4$ there exists a Cantor set $K_\tau\subset(1,2)$ such that each $\xi\in K_\tau$ has irrationality exponent $\mu(\xi)=\tau$ and infinitely many regular continued-fraction convergents of the form $2^a/3^b$.

The central ingredient is a counting estimate. Define

$$
\alpha=\frac{\log3}{\log2},\qquad
R(b)=\frac{2^{\lceil b\alpha\rceil}}{3^b},
$$

and let $\mathcal D$ be the set of denominators of the regular continued-fraction convergents of $\alpha$. For $4<\nu\le5$, let $E_N(D,\nu)$ count the indices $b\in[N,2N)$ for which some reduced $u/v\in[1,2]$, different from $R(b)$, satisfies

$$
v>D,\qquad
\left|R(b)-\frac uv\right|<\frac1{16v^\nu}.
$$

**Proposition 2.1** asserts that there is an absolute constant $C>0$ such that

$$
\limsup_{\substack{N\to\infty\\N\in\mathcal D}}
\frac{E_N(D,\nu)}{N}\le C D^{2-\nu}
\qquad(4<\nu\le5,\ D\ge2).
$$

The proof combines distribution of irrational rotations, the $p$-adic Subspace Theorem, product-set estimates, rational-power classes, and lower bounds for linear forms in logarithms.

## Formalization progress

| Mathematical component | Status |
| --- | --- |
| Prescribed fractions and reduced rational arithmetic | **Verified locally** |
| Finite counting and admissible-choice deduction | **Verified locally, conditional on the counting estimate** |
| Unbounded convergent denominators | **Verified locally** |
| Rotation discrepancy for the intervals used in the construction | **Verified locally** |
| Small-denominator bound (Lemma 3.1; absolute constant 60) | **Verified locally** |
| Height bound and logarithmic escape (Lemma 3.2) | **Verified locally, conditional on the Subspace Theorem** |
| Products of exceptional rational approximants (Lemma 3.3) | **Verified locally** |
| Classes modulo rational powers (Lemma 3.4) | **Verified locally** |
| Size of a power class (Lemma 3.5) | **Verified locally, conditional on weighted Matveev** |
| Count in a denominator range (Lemma 3.6) | **Verified locally, conditional on weighted Matveev** |
| Global summation and Proposition 2.1 (Gate 10; C=60) | **Verified locally, conditional on Subspace Theorem and Matveev** |
| Successor selection from Proposition 2.1 | **Verified locally, under the same external inputs** |
| Nested, disjoint successor intervals (Gate 11) | **Verified locally, conditional on Subspace Theorem and Matveev** |
| Coherent binary tree and uniform interval decay (Gate 12) | **Verified locally, conditional on the same two external results** |
| Infinite branch limits and Cantor topology (Gate 13) | **Verified locally, conditional on the same two external results** |
| Full rotation lemma for arbitrary circle arcs | Not yet formalized in full |
| Proposition 2.1 | **Verified locally, conditional on two external mathematical results** |
| Cantor topology (Gate 13) | **Verified locally, conditional on the two external results** |
| Irrationality, prescribed regular convergents and exact irrationality exponent | Not yet formalized |

The completed local developments comprise Gates 01–13. *Verified locally* refers to successful Lean builds and declaration audits documented in their reports; the proof sources have **not yet been uploaded to this repository or reproduced by its CI**. The counting proposition is locally verified **as an implication from two explicit external hypotheses**, not independently certified by repository CI. Gate 11 establishes two strictly nested, pairwise disjoint admissible successor intervals with uniform width contraction. Gate 12 uses those results to construct one coherent tree indexed by finite binary words, with interval widths bounded by the initial width divided by `81^n` at depth `n`. Gate 13 additionally proves unique limits for every infinite binary branch, continuous injective parametrization, a compact perfect nowhere-dense Cantor image in `(1,2)`, and exact strict displacement inequalities for the prescribed fractions. Irrationality of those limits, prescribed regular convergents, and their exact irrationality exponents remain unformalized.

The [formalization status](FORMALIZATION_STATUS.md) records the precise established statements, remaining mathematical inputs, and the relationship between local verification and repository verification. The table above will be updated only after checking the relevant theorem types and builds.

## Reproducibility

The development uses Lean 4 and mathlib with pinned dependencies. Once the local Lean sources have been imported, the [CI workflow](.github/workflows/lean.yml) will compile the project, inspect proof dependencies, and check the identity of the manuscript files. Until then, no successful GitHub build is claimed.

The published mathematical theorems used as external inputs must either be formalized or retained as explicit hypotheses in the types of the results that depend on them. Compilation alone does not discharge an ordinary theorem hypothesis.

## Citation

Please cite the manuscript for the mathematical results. Once a formally verified release is available, its immutable Git commit or release tag will identify the exact code and dependency versions used for reproducibility.

The repository is maintained as a mathematical research companion, not as a substitute for independent peer review.
