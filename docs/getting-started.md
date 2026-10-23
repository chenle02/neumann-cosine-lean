---
title: "Get started"
description: "Build and verify neumann-cosine-lean, and depend on it from another Lake project."
---

# Get started

## Build and verify

Toolchain Lean `v4.35.0` ([`lean-toolchain`](https://github.com/chenle02/neumann-cosine-lean/blob/main/lean-toolchain)); Mathlib `v4.35.0`, commit
`56a005855ea17e0b0958f73ec801ae140b0a1679` ([`lake-manifest.json`](https://github.com/chenle02/neumann-cosine-lean/blob/main/lake-manifest.json)).

```sh
git clone https://github.com/chenle02/neumann-cosine-lean.git
cd neumann-cosine-lean
lake exe cache get
lake build
```

To use it from another Lake project with the same toolchain:

```toml
[[require]]
name = "neumann-cosine-lean"
git = "https://github.com/chenle02/neumann-cosine-lean.git"
rev = "v0.1.0"
```

then `lake update neumann-cosine-lean`, `lake exe cache get`, and `import NeumannCosine` (or one module
from the table above). The trusted comparator statements are in
[`NeumannCosine/Challenge.lean`](https://github.com/chenle02/neumann-cosine-lean/blob/main/NeumannCosine/Challenge.lean); their `sorry` is intentional.

## Trust and axioms

The library modules contain no `sorry`, `axiom`, `opaque` or `native_decide`. The permitted axioms are
`propext`, `Classical.choice` and `Quot.sound`. The comparator checks that each headline proof proves exactly
its Mathlib-only restatement in `HeadlineChallenge.lean` (and `Challenge.lean` for the full set), and independent kernels replay it. No tool checks that the
prose in this README describes the Lean statements. The recorded results and receipts are in the
verification section at the end of this README.
