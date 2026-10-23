---
title: "Acknowledgments and citation"
description: "Authors, tools, compute and related work behind neumann-cosine-lean, and how to cite it."
---

# Acknowledgments and citation

## Authors and AI disclosure

Le Chen, Associate Professor, Department of Mathematics and Statistics, Auburn University.
The Lean code was developed with AI assistance under the author's direction. Lean compilation and an
independent kernel comparison check the stated theorems only; AI assistance is not human mathematical
review. Mathlib retains its own notices (see [NOTICE](https://github.com/chenle02/neumann-cosine-lean/blob/main/NOTICE)).

## lean-pkg

Developed and verified with [lean-pkg](https://github.com/lean-pkg/lean-pkg)
([doi:10.5281/zenodo.23272098](https://doi.org/10.5281/zenodo.23272098)). The receipts under
[`.lean-receipts/`](https://github.com/chenle02/neumann-cosine-lean/tree/main/.lean-receipts/) bind the checks to a source commit, and the verification section below
is rendered by `lean-pkg page` from [`coverage.yaml`](https://github.com/chenle02/neumann-cosine-lean/blob/main/coverage.yaml), [`claims.yaml`](https://github.com/chenle02/neumann-cosine-lean/blob/main/claims.yaml) and those
receipts; `lean-pkg page neumann-cosine-lean --check` confirms it is current.

## Auburn University Easley Cluster

This work was completed in part with resources provided by the [Auburn University Easley Cluster](https://hpc.auburn.edu/hpc/docs/hpcdocs/build/html/easley/intro.html).

The release build gates ran there as Slurm jobs; their receipts are committed under `.lean-receipts/` and listed on the [verification page](https://github.com/chenle02/neumann-cosine-lean/blob/main/verification.html).

## Built on

- [Mathlib](https://github.com/leanprover-community/mathlib4): The mathlib Community, *The Lean Mathematical
  Library*, CPP 2020, [doi:10.1145/3372885.3373824](https://doi.org/10.1145/3372885.3373824). Through Mathlib:
  [Batteries](https://github.com/leanprover-community/batteries),
  [Aesop](https://github.com/leanprover-community/aesop),
  [Qq](https://github.com/leanprover-community/quote4),
  [Plausible](https://github.com/leanprover-community/plausible),
  [ProofWidgets4](https://github.com/leanprover-community/ProofWidgets4),
  [LeanSearchClient](https://github.com/leanprover-community/LeanSearchClient),
  [import-graph](https://github.com/leanprover-community/import-graph) and
  [lean4-cli](https://github.com/leanprover/lean4-cli).
- [Lean 4](https://github.com/leanprover/lean4), including `leanchecker` (replay of the compiled proofs) and
  the `con-ron` kernel checker shipped in the toolchain.
- [comparator](https://github.com/leanprover/comparator) with
  [lean4export](https://github.com/leanprover/lean4export) and the
  [nanoda](https://github.com/robsimmons/nanoda_lib) kernel, for the statement comparison.


## Related work

These projects formalize nearby results. No code from them is used here.

- [xiangyazi24/Shen_work](https://github.com/xiangyazi24/Shen_work) (Xiang Huang): a continuum Neumann cosine
  layer on $`[0,1]`$ for $`C^2`$ functions, with coefficient decay and pointwise inversion at interior points.
  The repository has no license.
- The one-dimensional weak-derivative file of the Escauriaza–Seregin–Šverák formalization,
  [scottnarmstrong/EscauriazaSereginSverak](https://github.com/scottnarmstrong/EscauriazaSereginSverak/blob/main/ESS/Witnesses/WeakDerivOneDim.lean),
  also collected in [LeanPool](https://github.com/LeanPool/lean-pool/blob/main/LeanPool/EscauriazaSereginSverak/Witnesses/WeakDerivOneDim.lean).
  It proves independently that a weak derivative gives an absolutely continuous primitive.
- [TauCeti](https://github.com/TauCetiProject/TauCeti/blob/main/TauCeti/Analysis/Fourier/AbsolutelyContinuous.lean):
  Fourier coefficients of absolutely continuous functions on the circle, by integration by parts.
- [jinshanmu/Hatano-Nelson](https://github.com/jinshanmu/Hatano-Nelson): the sine eigenbasis and spectrum of
  tridiagonal Toeplitz matrices, the Dirichlet analogue of item 10.


## How to cite

Cite the software with [CITATION.cff](https://github.com/chenle02/neumann-cosine-lean/blob/main/CITATION.cff) ([doi:10.5281/zenodo.23488175](https://doi.org/10.5281/zenodo.23488175)).
