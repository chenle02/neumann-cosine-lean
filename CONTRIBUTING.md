# Contributing to NeumannCosine

Thank you for your interest. Small, explicit interfaces make the library easy to reuse.

## Before you start

- Read README.md, AGENTS.md and the Lean declarations you will touch.
- Use the pinned Lean toolchain and Mathlib manifest together. Run `lake exe cache get`, then `lake build`.
- Open an issue first for a new module or a change of scope.

## A good change

- States the mathematics in one or two sentences, with all hypotheses.
- Compiles locally with no `sorry` and only the standard axioms (`propext`, `Quot.sound`,
  `Classical.choice`).
- Follows Mathlib naming and style. Proofs should be readable, not only correct.
- Adds a short module docstring for a new file and a docstring for each main theorem.
- Updates `claims.yaml`, the README headline list and `coverage.yaml` when a public result changes.
- Keeps every hypothesis, including positivity of `L`, of the mesh size `N` and of the mode index.

## Provenance and license

All contributions are under Apache-2.0. Keep the copyright headers and the NOTICE file. If you adapt code
from another project, say so in the file header and check that its license allows it. Say clearly when a
result is a known theorem; this library formalizes classical analysis.

## Good first projects

- A general bridge from the cosine coefficients to Mathlib's `fourierCoeff` of the even `2L`-periodic
  extension (planned for v0.2).
- Upstreaming the general-`L` orthogonality of the cosine modes (`integral_mode_mul_mode`) to Mathlib.
- `L²` completeness of the cosine system and Parseval's identity.
