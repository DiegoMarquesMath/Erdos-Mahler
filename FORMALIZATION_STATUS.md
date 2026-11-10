# Scope and status of the formalization

This note identifies the mathematical statements established in the Lean development, the external results on which they depend, and the present limits of reproducibility. It is not a log of the development sessions.

## Principal statements

Let $\alpha=(\log 3)/(\log 2)$ and $R(b)=2^{\lceil b\alpha\rceil}/3^b$.

The quantitative argument leads to Proposition 2.1: for $4<\nu\leq5$ and $D\geq2$,

$$
\limsup_{\substack{N\to\infty\\N\in\mathcal D}}
\frac{E_N(D,\nu)}{N}\leq CD^{2-\nu},
$$

with one absolute constant $C$. The local formalization reports the explicit choice $C=60$ in `Gate10.proposition_2_1`, conditional on the two external results stated below.

The culminating declaration `Gate16.erdos_mahler_main` proves, under the same two hypotheses, that every real $\tau\geq4$ admits a nonempty compact Cantor set $K_\tau\subset(1,2)$ such that each $\xi\in K_\tau$ is irrational, has exact irrationality exponent $\tau$, and has infinitely many distinct regular continued-fraction convergents with numerator a power of $2$ and denominator a power of $3$.

Here the exponent is defined as the supremum, in the extended nonnegative reals, of the positive approximation orders admitting infinitely many distinct reduced rational approximants. The upper bound uses finiteness at every order greater than $\tau$; the lower bound uses infinitude at every smaller positive order. Neither argument assumes that the supremum is attained.

## Organization of the proof

| Modules | Mathematical content |
| --- | --- |
| Gates 01–04 | Rational arithmetic, rotation estimates, admissible choices, and the small-denominator count |
| Gates 05–10 | Height estimates, product sets, rational-power classes, logarithmic bounds, and Proposition 2.1 |
| Gates 11–13 | Successor intervals, a coherent binary tree, and the Cantor embedding |
| Gates 14–16 | Irrationality, actual regular convergents, estimates for arbitrary rationals, and the exact exponent |

The implementation uses a specialized interval-discrepancy estimate. The more general all-arcs formulation in the manuscript is not separately formalized and is not an additional premise of the final theorem.

## Two external mathematical inputs

The final theorem begins with precisely these two ordinary propositions:

1. **`Gate05.SubspaceTwoThreePrimitive`.** For each $0<\delta<1$, a specified set of primitive positive integer pairs satisfying a small local-product inequality is finite. The local-product expression is $|x-y|y/\operatorname{smoothPart}(xy)$, where the smooth part is supported on $\{2,3\}$.
2. **`Gate08.MatveevRationalThree`.** There is one positive constant $C_0$ providing the required lower bound for a nonzero linear form $\Lambda=\sum_{i=1}^3m_i\log\gamma_i$ in logarithms of positive rationals, subject to the specified height constraints, with
   $$
   \log|\Lambda|>-C_0A_1A_2A_3(1+\log B),\qquad
   B=\max\left\{1,\frac{|m_1|A_1}{A_3},\frac{|m_2|A_2}{A_3},|m_3|\right\}.
   $$

Neither proposition is asserted as an axiom of Lean. Both are **explicit assumptions in the type of the concluding theorem**. Their precise deduction from published results still requires an independent mathematical audit or a formal proof. An axiom audit listing only `propext`, `Classical.choice`, and `Quot.sound` does not discharge ordinary theorem parameters.

## Verification boundary

The reports from the author's local development record successful `lake build` and `Gate16Checks.lean` executions with the pinned toolchain. They also report source-preservation checks, stored proof bodies, and inspection of 682 project declarations reachable through the final theorem. These are records of a **local conditional formalization**, not certificates issued by an independent build.

At the time of this update, no Lean sources have been committed to the remote repository, and GitHub Actions has not reproduced the development. The canonical final Lean statement allows integer exponents $A,B\in\mathbb N$; the manuscript specifies positive exponents, for which a literal public corollary is still desirable.

The remaining certification work is to publish and reproduce the exact sources, inspect their correspondence with the frozen manuscript, and justify or formalize the two external mathematical inputs. None of those steps should be conflated with proving the conditional implication.
