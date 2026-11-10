# External theorems: precise specializations

The Lean development uses two published Diophantine estimates as explicit
premises. This note proves the mathematical reductions from their original
statements to the propositions appearing in the Lean types. It is not a
formalization of either published theorem in the Lean kernel.

## 1. Schlickewei and the primitive-pair finiteness statement

**Source.** H. P. Schlickewei, *The quantitative subspace theorem for number
fields*, *Compositio Mathematica* **82** (1992), 245–273, printed p. 246,
(1.3)–(1.5); [original article](https://www.numdam.org/item/CM_1992__82_3_245_0/).
The cited page reproduces the rational-integral case from Schlickewei's
earlier paper [10] (1990).

**Formal target.** `ErdosMahlerAudit.Gate05.SubspaceTwoThreePrimitive`,
defined in `ErdosMahlerAudit/Gate05/ExternalContract.lean`. For every
$0<\delta<1$ it asserts finiteness of the positive primitive integer pairs
$(x,y)$ for which

$$
\frac{|x-y|\,y}{2^{v_2(xy)}3^{v_3(xy)}}
<(x^2+y^2)^{-\delta/2}.
\tag{S}
$$

The denominator on the left is precisely `Gate05.smoothPart (x*y)`;
the full left-hand side is `Gate05.localProduct x y`.

**Reduction.** Apply the p-adic Subspace Theorem as stated in Schlickewei's
(1.3)–(1.5), with $K=\mathbb Q$, $n=2$ and
$S=\{\infty,2,3\}$. At these places choose, respectively,

$$
(L_{1,\infty},L_{2,\infty})=(X-Y,Y),\qquad
(L_{1,p},L_{2,p})=(X,Y)\quad(p=2,3).
$$

Every coefficient determinant is $1$. With the usual normalization
$|p|_p=p^{-1}$ and the Euclidean norm
$\|(x,y)\|=(x^2+y^2)^{1/2}$, the product appearing in (1.3) is

$$
\begin{aligned}
\prod_{v\in S}|L_{1,v}(x,y)L_{2,v}(x,y)|_v
 &=|x-y|\,y\,|xy|_2|xy|_3\\
 &=\frac{|x-y|\,y}{2^{v_2(xy)}3^{v_3(xy)}}.
\end{aligned}
$$

Thus (S) is exactly the inequality (1.3), with the same $\delta$.
Equations (1.4)–(1.5) place every such integral point either in one of
finitely many proper rational linear subspaces of $\mathbb Q^2$ or in a
bounded Euclidean ball. The latter contains finitely many integer points.
Every proper one-dimensional rational subspace contains at most one
**positive primitive** integer vector: if $(x,y)$ and $(x',y')$ lie on the
same line, then $xy'=x'y$, and their respective coprimality conditions force
$(x,y)=(x',y')$. The zero subspace contains none.

It follows that the set in (S) is finite. This is exactly the proposition
used in Gate 05; no additional exceptional-set or uniformity assumption
is needed.

## 2. Matveev and the weighted three-logarithm estimate

**Source.** E. M. Matveev, *An explicit lower bound for a homogeneous rational
linear form in the logarithms of algebraic numbers. II*, *Izvestiya:
Mathematics* **64** (2000), 1217–1269, printed pp. 1218–1219,
(1.3), (2.4), Corollary 2.3 and (2.6);
[original article](https://doi.org/10.1070/IM2000v064n06ABEH000314).

**Formal target.** `ErdosMahlerAudit.Gate08.MatveevRationalThree`,
defined in `ErdosMahlerAudit/Gate08/Height.lean`. For
$\gamma_i\in\mathbb Q_{>0}\setminus\{1\}$, $m_i\in\mathbb Z$, and

$$
A_i\ge\max\{h(\gamma_i),|\log\gamma_i|,0.16\},\qquad
h(\gamma)=\log\max\{|\operatorname{num}\gamma|,
                          \operatorname{den}\gamma\},
$$

put

$$
\Lambda=\sum_{i=1}^3m_i\log\gamma_i,\qquad
B=\max\left\{1,\frac{|m_1|A_1}{A_3},
              \frac{|m_2|A_2}{A_3},|m_3|\right\}.
$$

The proposition asks for **one absolute constant** $C_0>0$ such that
$\Lambda\neq0$ implies

$$
\log|\Lambda|>-C_0A_1A_2A_3(1+\log B).
\tag{M}
$$

**Reduction.** Specialize Corollary 2.3 to the real field
$K=\mathbb Q$ ($D=\kappa=1$) and three logarithms ($n=3$).
For positive rationals the absolute logarithmic height is the expression
for $h(\gamma)$ displayed above; its equality with the mathlib
logarithmic height is already proved as
`Gate08.rationalHeight_eq_library`. Condition (2.4) of Matveev is
exactly the condition on the three $A_i$. Since $A_3\ge0.16>0$, the last
term of the Lean maximum, $|m_3|A_3/A_3$, equals $|m_3|$.

Matveev's (1.3) supplies precisely the **weighted** $B$ above,
and Corollary 2.3 is stated for an arbitrary nonzero $\Lambda$; it
does not require the three logarithms to be independent. Equation (2.6)
provides $C_1(3,1)\le2^{6\cdot3+20}=2^{38}$ and

$$
\log|\Lambda|>
-C_1(3,1)D^2 A_1A_2A_3\log(eD)\log(eB).
$$

Since $D=1$, $\log(eD)=1$ and $\log(eB)=1+\log B$. Hence (M) holds
with the universal choice $C_0=2^{38}$. Vanishing coefficients and
multiplicatively dependent bases are permitted as long as
$\Lambda\neq0$. The additional restriction $\gamma_i\neq1$ in the Lean
contract is harmless.

## Scope of this verification

The reductions above compare the **exact Lean propositions** with the
published source theorems. They justify those propositions as classical
mathematical results. They do **not** construct proof terms for
`SubspaceTwoThreePrimitive` or `MatveevRationalThree`, nor
do they change the type of `Gate16.erdos_mahler_main`. Those two
propositions remain ordinary, explicit hypotheses of the locally checked
final theorem. The project's source publication and independent CI build
are separate reproducibility tasks.
