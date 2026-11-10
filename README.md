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

The Lean development covers the counting argument, the construction of a nested binary interval tree, the resulting Cantor set, the continued-fraction assertions, and the exact irrationality exponent. Its concluding declaration is

`ErdosMahlerAudit.Gate16.erdos_mahler_main`.

The formalization uses two established results in Diophantine approximation: Schlickewei's $p$-adic Subspace Theorem and Matveev's lower bound for linear forms in logarithms. Their exact specializations are justified in [External theorems](docs/EXTERNAL_THEOREMS.md). Since the original proofs of these classical results are not formalized in Lean, they appear as explicit premises in the concluding declaration. The precise scope of that declaration is recorded in [Formalization status](FORMALIZATION_STATUS.md).

The complete sources are published under [`formalization/ErdosMahlerAudit`](formalization/ErdosMahlerAudit). The pinned development passed its [independent GitHub Actions verification](https://github.com/DiegoMarquesMath/Erdos-Mahler/actions/runs/42761925776) at commit [`cb25517`](https://github.com/DiegoMarquesMath/Erdos-Mahler/commit/cb2551739d9e7d3e12ff0d16b8f3e182929f66bf).

For the exact logical boundary, see [Formalization status](FORMALIZATION_STATUS.md). For the pinned build and source identity, see [Reproducibility](docs/REPRODUCIBILITY.md).

## Citation

For mathematical results, cite the accompanying manuscript. For the formal development, cite the verified repository revision and its pinned dependencies.
