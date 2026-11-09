# Reproducing the Lean formalization

The current source code lives in a locally compiled Lean project until it is imported into this repository. The commands in this document become executable after `formalization/ErdosMahlerAudit/` has been populated.

## Pinned development

The local audit reports specify Lean `leanprover/lean4:v4.36.0-rc2` and mathlib revision `9d581dfff2e41de989072ea63abf3daf69311520`. The repository will preserve the exact existing `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`; dependency updates must be isolated from proof changes.

## Build

```bash
git clone https://github.com/DiegoMarquesMath/Erdos-Mahler.git
cd Erdos-Mahler/formalization/ErdosMahlerAudit

lake exe cache get
lake build

lake env lean ErdosMahlerAudit/Gate01Checks.lean
lake env lean ErdosMahlerAudit/Gate02Checks.lean
lake env lean ErdosMahlerAudit/Gate03Checks.lean
```

The checks files inspect the elaborated theorem statements and their axiom dependencies. The full theorem types must be read: an ordinary hypothesis does not appear as a kernel axiom.

## Reproducible source boundary

The Lean modules correspond to the version of `Erdos_Mahler.tex` and `Erdos_Mahler.pdf` whose SHA-256 hashes are recorded in [FORMALIZATION_STATUS.md](../FORMALIZATION_STATUS.md).

Proof obligations that are not yet discharged must remain as explicit theorem parameters or open tasks. In particular, a successful build of the current conditional successor theorem is not a formal proof of Proposition 2.1 or of the final Cantor-set theorem.

## Continuous integration

The [Lean workflow](../.github/workflows/lean.yml) will run on source-tree changes. It checks the pinned project, compiles all imported proof modules, executes the three gate checks, audits foundational axioms, and verifies the frozen manuscript identity.

A passing workflow establishes that its **committed source files** build with the pinned dependencies. Claims of complete formalization additionally require that the displayed mathematical statements match the manuscript and that no essential unproved hypothesis remains.
