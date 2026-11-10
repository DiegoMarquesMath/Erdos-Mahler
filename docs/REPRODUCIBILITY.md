# Reproducibility

The project is developed with Lean 4 and mathlib at fixed revisions. This document concerns source reproduction; the logical scope of the resulting theorem is given in [Formalization status](../FORMALIZATION_STATUS.md).

## Pinned versions

- Lean: `leanprover/lean4:v4.36.0-rc2`.
- mathlib: `9d581dfff2e41de989072ea63abf3daf69311520`.

The source publication will include the original `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`. An update to these files requires a separate reproducibility review.

## Independent build

After the Lean source tree has been published:

```bash
git clone https://github.com/DiegoMarquesMath/Erdos-Mahler.git
cd Erdos-Mahler/formalization/ErdosMahlerAudit
lake exe cache get
lake build
for gate in {01..16}; do
  lake env lean "ErdosMahlerAudit/Gate${gate}Checks.lean"
done
```

The [continuous-integration workflow](../.github/workflows/lean.yml) is configured to build with pinned dependencies, execute the gate checks, audit foundational axioms, and check the manuscript hashes. It has not yet run against the published source tree.

The principal theorem is `ErdosMahlerAudit.Gate16.erdos_mahler_main`. The exact type must be inspected alongside `#print axioms`: its explicit Subspace-Theorem and Matveev propositions are ordinary premises, not kernel axioms.

## Frozen manuscript

The local source bundle records the following SHA-256 digests:

```text
Erdos_Mahler.tex  5a55f32babc285ed9ad05fcb3bd6f8fe2bd3080d9eca7fd11e79ba23f7307116
Erdos_Mahler.pdf  9d9558f33236b6c1d7b276876153bf3d87f6fac2019c6e39db4d988e5022927f
```

These identify the manuscript copies to which the formalization refers. Their verification is a source-integrity check, not an independent assessment of the mathematical proof.

A passing CI run will establish reproducibility of a **conditional** formal result for a particular Git revision. The two exact external contracts are mathematically reduced to the published results of Schlickewei and Matveev in [External theorems](EXTERNAL_THEOREMS.md); they remain ordinary unproved Lean premises. A fully kernel-closed theorem would also require their formal proofs.
