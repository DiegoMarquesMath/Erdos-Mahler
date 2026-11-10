# A counterexample to the Erdős–Mahler conjecture

**Diego Marques**  
Universidade de Brasília

Lean 4 formalization accompanying the manuscript *A counterexample to the Erdős–Mahler conjecture*.

## The theorem

The manuscript establishes that, for every real number $\tau\geq 4$, there is a Cantor set $K_\tau\subset(1,2)$ such that every $\xi\in K_\tau$ has irrationality exponent $\mu(\xi)=\tau$ and infinitely many regular continued-fraction convergents of the form

$$
\frac{2^a}{3^b},\qquad a,b\geq 1.
$$

Thus the occurrence of convergents supported on a fixed finite set of primes does not force an irrational number to be Liouville.

## The counting theorem

Write

$$
\alpha=\frac{\log 3}{\log 2},\qquad
R(b)=\frac{2^{\lceil b\alpha\rceil}}{3^b},
$$

and let $\mathcal D$ denote the denominators of the regular continued-fraction convergents of $\alpha$. For $4<\nu\leq 5$ and $D\geq 2$, let $E_N(D,\nu)$ count those $b\in[N,2N)$ for which there is a reduced rational $u/v\in[1,2]$, different from $R(b)$, with

$$
v>D,\qquad
\left|R(b)-\frac uv\right|<\frac{1}{16v^\nu}.
$$

The central estimate (Proposition 2.1) is

$$
\limsup_{\substack{N\to\infty\\N\in\mathcal D}}
\frac{E_N(D,\nu)}{N}\leq CD^{2-\nu},
$$

where $C$ is absolute. The proof combines irrational rotations, additive and multiplicative estimates, the $p$-adic Subspace Theorem, and lower bounds for linear forms in logarithms.

## Formalization

The local Lean development covers the counting argument, the construction of a nested binary interval tree, the resulting Cantor set, the continued-fraction assertions, and the exact irrationality exponent. Its concluding declaration is

`ErdosMahlerAudit.Gate16.erdos_mahler_main`.

**The formal theorem is conditional.** Its two ordinary mathematical hypotheses are `Gate05.SubspaceTwoThreePrimitive` and `Gate08.MatveevRationalThree`. These are mathematically derived from the published theorems of Schlickewei and Matveev in [External theorems](docs/EXTERNAL_THEOREMS.md); the reductions are documented, not proved in Lean. The formal conclusion currently quantifies powers with nonnegative integer exponents. A positive-exponent strengthening, matching the manuscript literally, remains to be stated in the public Lean theorem.

The 16 stages have passed the reported local Lean checks. The sources have **not yet been committed to this repository**, and an independent GitHub Actions build has **not yet been obtained**. A successful build will verify the conditional implication, not discharge its two hypotheses.

For the exact logical boundary, see [Formalization status](FORMALIZATION_STATUS.md). For the pinned build and source identity, see [Reproducibility](docs/REPRODUCIBILITY.md).

## Citation

For mathematical results, cite the accompanying manuscript. For the formal development, cite a fixed repository revision after its sources have been published and independently reproduced.
