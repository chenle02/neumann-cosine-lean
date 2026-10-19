<div align="center">

# Neumann Cosine

Neumann cosine series on an interval $`[0,L]`$ and the discrete Neumann Laplacian: orthogonality, product integrals, summable coefficients and pointwise expansions under $`W^{2,1}`$ or $`H^2`$ Neumann data, and convergence of the discrete spectrum. Formalized in Lean 4 with Mathlib.

[![Lean](https://img.shields.io/badge/Lean-v4.35.0-153e63)](lean-toolchain)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.35.0-153e63)](https://github.com/leanprover-community/mathlib4/tree/56a005855ea17e0b0958f73ec801ae140b0a1679)
[![Release](https://img.shields.io/badge/release-v0.1.0-153e63)](https://github.com/chenle02/neumann-cosine-lean/releases/tag/v0.1.0)
[![License](https://img.shields.io/badge/license-Apache--2.0-153e63)](LICENSE)
[![arXiv](https://img.shields.io/badge/arXiv-2610.20976-153e63)](https://arxiv.org/abs/2610.20976)

[What is proved](#what-is-proved) · [Verification page](docs/verification.md) · [Build](#build-and-verify) · [Cite](CITATION.cff)

</div>

## What is proved

The mode of index $`k`$ is $`\cos(k\pi x/L)`$. The cosine coefficients of $`w`$ are
$`w_0=\frac1L\int_0^L w`$ and $`w_k=\frac2L\int_0^L w(x)\cos(k\pi x/L)\,dx`$ for $`k\ge1`$.
In every item $`L>0`$ unless stated otherwise. The results are classical analysis; no new mathematics
is claimed.

1. **Orthogonality.** $`\int_0^L\cos(m\pi x/L)\cos(n\pi x/L)\,dx`$ equals $`L`$ if $`m=n=0`$, $`L/2`$ if
   $`m=n\ge1`$, and $`0`$ if $`m\ne n`$.
   `NeumannCosine.integral_mode_mul_mode`
2. **Four-mode integral.** $`\int_0^L\cos_i\cos_j\cos_l\cos_k`$ equals $`L/8`$ times the number of the seven
   conditions $`i+j+l=k`$, $`i+j-l=\pm k`$, $`i-j+l=\pm k`$, $`i-j-l=\pm k`$ (in $`\mathbb Z`$) that hold, plus
   $`L/8`$ when $`i=j=l=k=0`$.
   `NeumannCosine.KernelIntegrals.integral_cos_cos_cos_cos`
3. **Three cosine series against a mode.** For $`u,v,w\in\ell^1(\mathbb N_0)`$ with cosine series $`U,V,W`$,
   $`\int_0^L UVW\cos(k\pi x/L)\,dx`$ is $`L/8`$ times the sum of the seven constrained convolutions
   $`\sum u_iv_jw_l`$ over the conditions of item 2, plus $`\frac L8u_0v_0w_0`$ when $`k=0`$.
   `NeumannCosine.ProductIdentities.cos_cos_cos_cos_lp`
4. **Two cosine series against two sines.** For $`u,v\in\ell^1(\mathbb N_0)`$ and $`n,k\ge1`$,
   $`\int_0^L UV\sin(n\pi x/L)\sin(k\pi x/L)\,dx`$ is $`L/8`$ times the constrained sums $`\sum u_iv_j`$ over
   $`i-j=\pm(n-k)`$ and $`i+j=\pm(n-k)`$, minus those over $`i-j=\pm(n+k)`$ and $`i+j=n+k`$.
   `NeumannCosine.ProductIdentities.two_cosines_two_sines_lp`
5. **Summable coefficients.** Let $`w`$ be absolutely continuous on $`[0,L]`$ with derivative $`w'`$ on
   $`(0,L)`$, let $`w'`$ be absolutely continuous on $`[0,L]`$, and let $`w'(0)=w'(L)=0`$ (the class
   `NeumannW21`). Then $`\sum_k|w_k|<\infty`$.
   `NeumannCosine.Coefficients.summable_norm_cosineCoeff`
6. **Pointwise expansion.** Under the same hypothesis, $`w(x)=\sum_{k\ge0}w_k\cos(k\pi x/L)`$ for every
   $`x\in[0,L]`$.
   `NeumannCosine.Coefficients.hasSum_cosineCoeff`
7. **du Bois-Reymond lemma.** If $`h\in L^1(0,L)`$ and $`\int_0^L h\varphi'=0`$ for every
   $`\varphi\in C_c^\infty(0,L)`$, then $`h`$ is a.e. constant on $`(0,L)`$.
   `NeumannCosine.Sobolev.WeakDerivative.ae_eq_const_of_integral_mul_deriv_eq_zero`
8. **$`W^{1,1}`$ functions are absolutely continuous.** If $`g\in L^1(0,L)`$ is the weak derivative of
   $`w\in L^1(0,L)`$, then $`w(x)=c+\int_0^x g`$ for a.e. $`x\in(0,L)`$. This representative is absolutely
   continuous on $`[0,L]`$, with derivative $`g(x)`$ at a.e. $`x`$.
   `NeumannCosine.Sobolev.WeakDerivative.HasWeakDeriv.ae_eq_primitive`
9. **$`H^2`$ with Neumann trace.** If $`w\in H^2(0,L)`$ and its weak derivative has a continuous
   representative vanishing at $`0`$ and $`L`$, then $`w`$ has a representative $`W`$, continuous on
   $`[0,L]`$, with $`W(x)=\sum_k w_k\cos(k\pi x/L)`$ for every $`x\in[0,L]`$.
   `NeumannCosine.Sobolev.H2Neumann.H2.hasSum_cosineCoeff`
10. **Discrete Neumann Laplacian.** On the grid $`0,1,\dots,N`$ with $`h=L/N`$ and reflected ghost points,
    the vector $`i\mapsto\cos(n\pi i/N)`$ satisfies $`(2u_i-u_{i-1}-u_{i+1})/h^2=\lambda_{n,N}u_i`$ with
    $`\lambda_{n,N}=\frac{4}{h^2}\sin^2\frac{n\pi}{2N}`$, for $`0\le n\le N`$. These $`N+1`$ vectors span all
    grid functions. Here $`L\ne0`$ and $`N\ge1`$.
    `NeumannCosine.Discrete.Laplacian.reflectedNegLaplacian_cosine_eigenpair`,
    `NeumannCosine.Discrete.Laplacian.discreteCosineMode_exhaustion`
11. **Eigenvalue convergence.** For each fixed $`n\ge1`$, $`\lambda_{n,N}\to(n\pi/L)^2`$ as $`N\to\infty`$.
    `NeumannCosine.Discrete.Eigenvalues.discreteNeumannEigenvalue_tendsto`
12. **Modal minimum.** Let $`f:\mathbb R\to\mathbb R`$ be continuous at every $`x>0`$, with $`Kx\le f(x)`$ for
    $`x>0`$ and some $`K>0`$. Then $`\min_{1\le n\le N}f(\lambda_{n,N})\to\inf_{n\ge1}f((n\pi/L)^2)`$ as
    $`N\to\infty`$.
    `NeumannCosine.Discrete.ModalMinimumLimit.discreteModalMin_tendsto`

Each Lean statement is the authority; read its hypotheses before you use it. The
[verification page](docs/verification.md) shows each Lean statement beside its description; the same page will be
rendered in the verification section at the end of this README once the release checks have run.

| Module | Contents |
|---|---|
| `NeumannCosine.Basic` | The mode, its frequency, orthogonality and Gram values |
| `NeumannCosine.Series.TermwiseIntegral` | Termwise integration of $`\ell^1`$ cosine series |
| `NeumannCosine.Series.Products` | Products of $`\ell^1`$ cosine series, interchange with the integral, signed-index reindexing |
| `NeumannCosine.KernelIntegrals` | Closed forms of integrals of products of three and four modes |
| `NeumannCosine.ProductIdentities` | Integrals of products of two to four cosine series as constrained convolutions |
| `NeumannCosine.Coefficients` | The class `NeumannW21`: $`O(k^{-2})`$ coefficients, summability, pointwise expansion |
| `NeumannCosine.Sobolev.WeakDerivative` | Weak derivatives on $`(0,L)`$, du Bois-Reymond, absolutely continuous representative |
| `NeumannCosine.Sobolev.H2Neumann` | $`H^2(0,L)`$ with Neumann trace lies in `NeumannW21` |
| `NeumannCosine.DivergenceFormProjection` | $`\lvert\int_0^L(R_0+R_1')\cos(k\pi x/L)\,dx\rvert\le(L+k\pi)B`$ when $`\lvert R_0\rvert,\lvert R_1\rvert\le B`$ on $`[0,L]`$, $`R_0`$ is integrable, $`R_1`$ is absolutely continuous on $`[0,L]`$ (or continuous on $`[0,L]`$ and differentiable at every point of $`(0,L)`$ with integrable derivative), and $`R_1(0)=R_1(L)=0`$ |
| `NeumannCosine.Discrete.Eigenvalues` | Discrete and continuum eigenvalues, $`\operatorname{sinc}^2`$ relation, convergence, lower bound |
| `NeumannCosine.Discrete.Laplacian` | The reflected three-point stencil on `Fin (N + 1)`, its cosine eigenvectors and basis |
| `NeumannCosine.Discrete.ModalMinimumTail` | One tail cutoff for all fine meshes, for a linearly coercive $`f`$ |
| `NeumannCosine.Discrete.ModalMinimumLimit` | The discrete modal minimum converges to the continuum infimum |

> [!IMPORTANT]
> **Not proved here.**
> - No PDE theory: no existence, uniqueness or regularity theorem for any differential equation, and no semigroup.
> - No $`L^2`$ theory: completeness of the cosine system in $`L^2(0,L)`$ and Parseval's identity for general $`L^2`$ functions are not proved. The expansions above need summable coefficients, which the library derives from $`W^{2,1}`$ or $`H^2`$ Neumann data.
> - No general bridge to Mathlib's `fourierCoeff`. `Coefficients.fourierCoeff_evenPeriodic` covers only the even $`2L`$-periodic extension of a `NeumannW21` function. A bridge for general integrable functions is planned for v0.2.
> - One dimension only: no domains in two or more dimensions.

## Paper and references

The library was first developed for the Lean companion of the paper below. It keeps only the general
mathematics; nothing in it depends on the paper.

L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent sensitivity and a logistic-type
source, III: Bifurcation and spike-like solutions*, preprint, 2026.
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976).

```bibtex
@article{chen.ruau.ea:26:bifurcation,
  title         = {Chemotaxis models with signal-dependent sensitivity and a logistic-type source, {III}: Bifurcation and spike-like solutions},
  author        = {Chen, Le and Ruau, Ian and Shen, Wenxian},
  year          = {2026},
  month         = {October},
  journal       = {Preprint arXiv:2610.20976},
  eprint        = {2610.20976},
  archiveprefix = {arXiv},
  primaryclass  = {math.AP},
  url           = {https://arxiv.org/abs/2610.20976}
}
```

`NeumannCosine/Basic.lean` contains portions first published by Le Chen under the MIT license in
[chenle02/Chemataxis_Numerics](https://github.com/chenle02/Chemataxis_Numerics). He relicensed them under
Apache-2.0 for this library; see [NOTICE](NOTICE).

**Related work.** These projects formalize nearby results. No code from them is used here.

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

## Build and verify

Toolchain Lean `v4.35.0` ([`lean-toolchain`](lean-toolchain)); Mathlib `v4.35.0`, commit
`56a005855ea17e0b0958f73ec801ae140b0a1679` ([`lake-manifest.json`](lake-manifest.json)).

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
[`NeumannCosine/Challenge.lean`](NeumannCosine/Challenge.lean); their `sorry` is intentional.

**Built on.**

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

## Trust and axioms

The library modules contain no `sorry`, `axiom`, `opaque` or `native_decide`. The permitted axioms are
`propext`, `Classical.choice` and `Quot.sound`. The comparator checks that each headline proof proves exactly
its Mathlib-only restatement in `HeadlineChallenge.lean` (and `Challenge.lean` for the full set), and independent kernels replay it. No tool checks that the
prose in this README describes the Lean statements. The recorded results and receipts will appear in the
verification section at the end of this README ("What the checks establish") once the release checks have run.

## Built with lean-pkg

Developed and verified with [lean-pkg](https://github.com/lean-pkg/lean-pkg)
([doi:10.5281/zenodo.23272098](https://doi.org/10.5281/zenodo.23272098)). The receipts in
`.lean-receipts/` (added with the first verified release) bind the checks to a source commit, and the verification section below
is rendered by `lean-pkg page` from [`coverage.yaml`](coverage.yaml), [`claims.yaml`](claims.yaml) and those
receipts; `lean-pkg page neumann-cosine-lean --check` confirms it is current.

## Authors and AI disclosure

Le Chen, Associate Professor, Department of Mathematics and Statistics, Auburn University.
The Lean code was developed with AI assistance under the author's direction. Lean compilation and an
independent kernel comparison check the stated theorems only; AI assistance is not human mathematical
review. Mathlib retains its own notices (see [NOTICE](NOTICE)).

<!-- lean-pkg:page:begin -->
<!-- lean-pkg:page:end -->
