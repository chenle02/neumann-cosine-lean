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
[verification page](docs/verification.md) shows each Lean statement beside its description; the same page is
rendered in the verification section at the end of this README.

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
prose in this README describes the Lean statements. The recorded results and receipts are in the
verification section at the end of this README.

## Built with lean-pkg

Developed and verified with [lean-pkg](https://github.com/lean-pkg/lean-pkg)
([doi:10.5281/zenodo.23272098](https://doi.org/10.5281/zenodo.23272098)). The receipts under
[`.lean-receipts/`](.lean-receipts/) bind the checks to a source commit, and the verification section below
is rendered by `lean-pkg page` from [`coverage.yaml`](coverage.yaml), [`claims.yaml`](claims.yaml) and those
receipts; `lean-pkg page neumann-cosine-lean --check` confirms it is current.

## Authors and AI disclosure

Le Chen, Associate Professor, Department of Mathematics and Statistics, Auburn University.
The Lean code was developed with AI assistance under the author's direction. Lean compilation and an
independent kernel comparison check the stated theorems only; AI assistance is not human mathematical
review. Mathlib retains its own notices (see [NOTICE](NOTICE)).

<!-- lean-pkg:page:begin -->
<!-- Generated by `lean-pkg page neumann-cosine-lean` from coverage.yaml, claims.yaml, the claims ledger and the receipts committed under .lean-receipts/. Do not edit between the markers: change the data and run `lean-pkg page neumann-cosine-lean --write`. -->

## Verification at a glance

**How to read this page.** Lean has checked every step of the proofs listed here. Each result is exactly its Lean statement: read the statements below to see what is proved. The titles, the words and the notes are the authors' description, which Lean does not check.

Neumann cosine modes on \[0, L\]: Gram values, closed-form product integrals, absolutely summable cosine expansions of W^{2,1} and H^2 functions with Neumann data, one-dimensional weak derivatives, and the discrete Neumann Laplacian with its convergence to the continuum spectrum.

- Main results: 20; verified: 20 of 20.

## Main results

### Orthogonality and Gram values of the Neumann cosine modes

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For $L>0$ and $m,n\in\mathbb N$,
\[\int_0^L \cos\frac{m\pi y}{L}\cos\frac{n\pi y}{L}\,dy=\begin{cases}L,& m=n=0,\\ L/2,& m=n\neq 0,\\ 0,& m\neq n.\end{cases}\]
```

**In Lean.** `NeumannCosineHeadline.NeumannCosine.integral_mode_mul_mode` in [NeumannCosine/HeadlineChallenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/HeadlineChallenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem integral_mode_mul_mode (L : ℝ) (hL : 0 < L) (m n : ℕ) :
    (∫ y in (0 : ℝ)..L,
      Real.cos ((m : ℝ) * Real.pi * y / L) * Real.cos ((n : ℝ) * Real.pi * y / L)) =
      if m = n then (if m = 0 then L else L / 2) else 0
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Closed form of the integral of four cosine modes

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For $L>0$, $i,j,l,k\in\mathbb N$ and $c_m(x)=\cos(m\pi x/L)$,
\[\int_0^L c_i c_j c_l c_k\,dx=\frac L8\Big(\mathbf 1_{i+j+l=k}+\mathbf 1_{i+j-l=k}+\mathbf 1_{i+j-l=-k}+\mathbf 1_{i-j+l=k}+\mathbf 1_{i-j+l=-k}+\mathbf 1_{i-j-l=k}+\mathbf 1_{i-j-l=-k}\Big)+\frac L8\,\mathbf 1_{i=j=l=k=0},\]
with the index arithmetic in $\mathbb Z$.
```

**In Lean.** `NeumannCosineHeadline.NeumannCosine.KernelIntegrals.integral_cos_cos_cos_cos` in [NeumannCosine/HeadlineChallenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/HeadlineChallenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem integral_cos_cos_cos_cos (L : ℝ) (hL : 0 < L) (i j l k : ℕ) :
    (∫ x in (0 : ℝ)..L,
      Real.cos ((i : ℝ) * Real.pi * x / L) * Real.cos ((j : ℝ) * Real.pi * x / L) *
        Real.cos ((l : ℝ) * Real.pi * x / L) * Real.cos ((k : ℝ) * Real.pi * x / L)) =
      L / 8 * ((if (i : ℤ) + j + l = k then 1 else 0) +
        (if (i : ℤ) + j - l = k then 1 else 0) +
        (if (i : ℤ) + j - l = -k then 1 else 0) +
        (if (i : ℤ) - j + l = k then 1 else 0) +
        (if (i : ℤ) - j + l = -k then 1 else 0) +
        (if (i : ℤ) - j - l = k then 1 else 0) +
        (if (i : ℤ) - j - l = -k then 1 else 0)) +
        L / 8 * (if k = 0 ∧ i = 0 ∧ j = 0 ∧ l = 0 then 1 else 0)
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Integral of a product of three cosine series against a cosine

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For $L>0$, $u,v,w\in\ell^1(\mathbb N)$ and $k\in\mathbb N$,
\[\int_0^L\Big(\sum_i u_i c_i\Big)\Big(\sum_j v_j c_j\Big)\Big(\sum_l w_l c_l\Big)c_k\,dx=\frac L8\sum_{\sigma}\ \sum_{i+\sigma_1 j+\sigma_2 l=\sigma_3 k}u_iv_jw_l+\frac L8\,\mathbf 1_{k=0}\,u_0v_0w_0,\]
where $c_m(x)=\cos(m\pi x/L)$ and $\sigma=(\sigma_1,\sigma_2,\sigma_3)$ runs over the seven sign patterns $(+,+,+)$, $(+,-,\pm)$, $(-,+,\pm)$, $(-,-,\pm)$; each inner sum is over $(i,j,l)\in\mathbb N^3$ with the constraint in $\mathbb Z$.
```

**In Lean.** `NeumannCosineHeadline.NeumannCosine.ProductIdentities.cos_cos_cos_cos_lp` in [NeumannCosine/HeadlineChallenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/HeadlineChallenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem cos_cos_cos_cos_lp (L : ℝ) (hL : 0 < L)
    (u v w : lp (fun _ : ℕ => ℝ) 1) (k : ℕ) :
    ∫ x in (0 : ℝ)..L,
        (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
          (∑' j : ℕ, v j * Real.cos ((j : ℝ) * Real.pi * x / L)) *
          (∑' l : ℕ, w l * Real.cos ((l : ℝ) * Real.pi * x / L)) *
          Real.cos ((k : ℝ) * Real.pi * x / L) =
      L / 8 *
        ((∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) + t.2.1 + t.2.2 = k},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) + t.2.1 - t.2.2 = k},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) + t.2.1 - t.2.2 = -(k : ℤ)},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 + t.2.2 = k},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 + t.2.2 = -(k : ℤ)},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 - t.2.2 = k},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 - t.2.2 = -(k : ℤ)},
            u t.1.1 * v t.1.2.1 * w t.1.2.2)) +
        L / 8 * (if k = 0 then u 0 * v 0 * w 0 else 0)
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Integral of two cosine series against two sines

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For $L>0$, $u,v\in\ell^1(\mathbb N)$ and $n,k\ge 1$, with $c_m(x)=\cos(m\pi x/L)$ and $s_m(x)=\sin(m\pi x/L)$,
\[\int_0^L\Big(\sum_i u_ic_i\Big)\Big(\sum_j v_jc_j\Big)s_ns_k\,dx=\frac L8\Big(\sum_{i-j=n-k}+\sum_{i-j=k-n}+\sum_{i+j=n-k}+\sum_{i+j=k-n}-\sum_{i-j=n+k}-\sum_{i-j=-(n+k)}-\sum_{i+j=n+k}\Big)u_iv_j,\]
each sum over $(i,j)\in\mathbb N^2$ with the constraint in $\mathbb Z$.
```

**In Lean.** `NeumannCosineHeadline.NeumannCosine.ProductIdentities.two_cosines_two_sines_lp` in [NeumannCosine/HeadlineChallenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/HeadlineChallenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem two_cosines_two_sines_lp (L : ℝ) (hL : 0 < L)
    (u v : lp (fun _ : ℕ => ℝ) 1) (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∫ x in (0 : ℝ)..L,
        (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
          (∑' j : ℕ, v j * Real.cos ((j : ℝ) * Real.pi * x / L)) *
          Real.sin ((n : ℝ) * Real.pi * x / L) *
          Real.sin ((k : ℝ) * Real.pi * x / L) =
      L / 8 *
        ((∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = (n : ℤ) - k},
            u p.1.1 * v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = -((n : ℤ) - k)},
            u p.1.1 * v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) + p.2 = (n : ℤ) - k},
            u p.1.1 * v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) + p.2 = -((n : ℤ) - k)},
            u p.1.1 * v p.1.2) -
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = (n : ℤ) + k},
            u p.1.1 * v p.1.2) -
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = -((n : ℤ) + k)},
            u p.1.1 * v p.1.2) -
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) + p.2 = (n : ℤ) + k},
            u p.1.1 * v p.1.2))
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Cosine coefficients of W^{2,1} Neumann functions are absolutely summable

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Let $L>0$ and let $w$ be absolutely continuous on $[0,L]$ with derivative $w'(x)$ at every $x\in(0,L)$, where $w'$ is absolutely continuous on $[0,L]$ and $w'(0)=w'(L)=0$. With $w_0=\frac1L\int_0^Lw$ and $w_k=\frac2L\int_0^Lw(x)\cos\frac{k\pi x}{L}\,dx$ for $k\ge1$,
\[\sum_{k\ge0}|w_k|<\infty.\]
```

**In Lean.** `NeumannCosineHeadline.NeumannCosine.Coefficients.summable_norm_cosineCoeff` in [NeumannCosine/HeadlineChallenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/HeadlineChallenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem summable_norm_cosineCoeff (L : ℝ) (hL : 0 < L) {w w' : ℝ → ℝ}
    (hac : AbsolutelyContinuousOnInterval w 0 L)
    (hderiv : ∀ x ∈ Ioo 0 L, HasDerivAt w (w' x) x)
    (hac' : AbsolutelyContinuousOnInterval w' 0 L)
    (hleft : w' 0 = 0) (hright : w' L = 0) :
    Summable fun k : ℕ =>
      ‖(if k = 0 then 1 / L else 2 / L) *
        ∫ x in (0 : ℝ)..L, w x * Real.cos ((k : ℝ) * Real.pi * x / L)‖
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Pointwise cosine expansion of W^{2,1} Neumann functions

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Under the hypotheses of the previous row, for every $x\in[0,L]$,
\[w(x)=\sum_{k\ge0}w_k\cos\frac{k\pi x}{L},\]
the series converging absolutely.
```

**In Lean.** `NeumannCosineHeadline.NeumannCosine.Coefficients.hasSum_cosineCoeff` in [NeumannCosine/HeadlineChallenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/HeadlineChallenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem hasSum_cosineCoeff (L : ℝ) (hL : 0 < L) {w w' : ℝ → ℝ}
    (hac : AbsolutelyContinuousOnInterval w 0 L)
    (hderiv : ∀ x ∈ Ioo 0 L, HasDerivAt w (w' x) x)
    (hac' : AbsolutelyContinuousOnInterval w' 0 L)
    (hleft : w' 0 = 0) (hright : w' L = 0) {x : ℝ} (hx : x ∈ Icc 0 L) :
    HasSum (fun k : ℕ =>
      ((if k = 0 then 1 / L else 2 / L) *
        ∫ y in (0 : ℝ)..L, w y * Real.cos ((k : ℝ) * Real.pi * y / L)) *
        Real.cos ((k : ℝ) * Real.pi * x / L)) (w x)
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### The du Bois-Reymond lemma on an interval

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Let $L>0$ and $h\in L^1(0,L)$. If $\int_0^L h\,\varphi'\,dx=0$ for every $\varphi\in C_c^\infty(0,L)$ (smooth, compactly supported, $\operatorname{tsupp}\varphi\subseteq(0,L)$), then there is $c\in\mathbb R$ with $h=c$ almost everywhere on $(0,L)$.
```

**In Lean.** `NeumannCosineHeadline.NeumannCosine.Sobolev.WeakDerivative.ae_eq_const_of_integral_mul_deriv_eq_zero` in [NeumannCosine/HeadlineChallenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/HeadlineChallenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem ae_eq_const_of_integral_mul_deriv_eq_zero {L : ℝ} (hL : 0 < L) {h : ℝ → ℝ}
    (hh : IntervalIntegrable h volume 0 L)
    (H : ∀ φ : ℝ → ℝ, (ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ioo 0 L) →
      ∫ x in (0 : ℝ)..L, h x * deriv φ x = 0) :
    ∃ c : ℝ, ∀ᵐ x, x ∈ Ioo 0 L → h x = c
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### W^{1,1} functions have an absolutely continuous representative

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Let $L>0$ and $w,g\in L^1(0,L)$ with $\int_0^Lw\,\varphi'\,dx=-\int_0^Lg\,\varphi\,dx$ for every $\varphi\in C_c^\infty(0,L)$. Then for some $c\in\mathbb R$ the function $W(x)=c+\int_0^xg(t)\,dt$ satisfies $w=W$ a.e. on $(0,L)$, $W$ is absolutely continuous on $[0,L]$, and $W'(x)=g(x)$ for almost every $x\in[0,L]$.
```

**In Lean.** `NeumannCosineHeadline.NeumannCosine.Sobolev.WeakDerivative.HasWeakDeriv.ae_eq_primitive` in [NeumannCosine/HeadlineChallenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/HeadlineChallenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem HasWeakDeriv.ae_eq_primitive {L : ℝ} (hL : 0 < L) {w g : ℝ → ℝ}
    (hw : IntervalIntegrable w volume 0 L) (hg : IntervalIntegrable g volume 0 L)
    (hwg : ∀ φ : ℝ → ℝ, (ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ioo 0 L) →
      ∫ x in (0 : ℝ)..L, w x * deriv φ x = -∫ x in (0 : ℝ)..L, g x * φ x) :
    ∃ c : ℝ, (∀ᵐ x, x ∈ Ioo 0 L → w x = c + ∫ t in (0 : ℝ)..x, g t) ∧
      AbsolutelyContinuousOnInterval (fun x => c + ∫ t in (0 : ℝ)..x, g t) 0 L ∧
      ∀ᵐ x, x ∈ Icc 0 L → HasDerivAt (fun x => c + ∫ t in (0 : ℝ)..x, g t) (g x) x
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Cosine expansion of H^2 functions with Neumann trace

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Let $L>0$ and $w,w_1,w_2\in L^2(0,L)$, with $w_1$ the weak derivative of $w$ and $w_2$ the weak derivative of $w_1$ (tested against $C_c^\infty(0,L)$). Suppose some $V$ continuous on $[0,L]$ equals $w_1$ a.e. on $(0,L)$ and $V(0)=V(L)=0$. Then there is $W$ continuous on $[0,L]$ with $W=w$ a.e. on $(0,L)$ and, for every $x\in[0,L]$,
\[W(x)=\sum_{k\ge0}w_k\cos\frac{k\pi x}{L},\]
where $w_k$ are the cosine coefficients of $w$ (as above).
```

**In Lean.** `NeumannCosineHeadline.NeumannCosine.Sobolev.H2Neumann.H2.hasSum_cosineCoeff` in [NeumannCosine/HeadlineChallenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/HeadlineChallenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem H2.hasSum_cosineCoeff {L : ℝ} (hL : 0 < L) {w w₁ w₂ : ℝ → ℝ}
    (hw : MemLp w 2 (volume.restrict (Ioo 0 L)))
    (hw₁ : MemLp w₁ 2 (volume.restrict (Ioo 0 L)))
    (hw₂ : MemLp w₂ 2 (volume.restrict (Ioo 0 L)))
    (hd₁ : ∀ φ : ℝ → ℝ, (ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ioo 0 L) →
      ∫ x in (0 : ℝ)..L, w x * deriv φ x = -∫ x in (0 : ℝ)..L, w₁ x * φ x)
    (hd₂ : ∀ φ : ℝ → ℝ, (ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ioo 0 L) →
      ∫ x in (0 : ℝ)..L, w₁ x * deriv φ x = -∫ x in (0 : ℝ)..L, w₂ x * φ x)
    (hN : ∃ V : ℝ → ℝ, ContinuousOn V (Icc 0 L) ∧ (∀ᵐ x, x ∈ Ioo 0 L → w₁ x = V x) ∧
      V 0 = 0 ∧ V L = 0) :
    ∃ W : ℝ → ℝ, (∀ᵐ x, x ∈ Ioo 0 L → w x = W x) ∧ ContinuousOn W (Icc 0 L) ∧
      ∀ x ∈ Icc 0 L, HasSum (fun k : ℕ =>
        ((if k = 0 then 1 / L else 2 / L) *
          ∫ y in (0 : ℝ)..L, w y * Real.cos ((k : ℝ) * Real.pi * y / L)) *
          Real.cos ((k : ℝ) * Real.pi * x / L)) (W x)
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Cosine eigenbasis of the discrete Neumann Laplacian

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Let $L\neq0$, $N\ge1$, $h=L/N$, and on the grid $\{0,\dots,N\}$ let $(\Delta_h u)_i=(2u_i-u_{i-1}-u_{i+1})/h^2$ with reflected ghost points $u_{-1}=u_1$, $u_{N+1}=u_{N-1}$. For $0\le n\le N$ the vector $u_j=\cos(n\pi j/N)$ satisfies
\[\Delta_h u=\frac{4}{h^2}\sin^2\frac{n\pi}{2N}\,u,\]
these $N+1$ cosine vectors are linearly independent, and every real function on the grid is a linear combination of them.
```

**In Lean.** `NeumannCosineHeadline.NeumannCosine.Discrete.Laplacian.reflectedNegLaplacian_cosine_eigenpair` in [NeumannCosine/HeadlineChallenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/HeadlineChallenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem reflectedNegLaplacian_cosine_eigenpair (L : ℝ) (N n : ℕ) (hL : L ≠ 0)
    (hN : 0 < N) (hnN : n ≤ N) (u : Fin (N + 1) → ℝ)
    (hu : ∀ j : Fin (N + 1), u j = Real.cos ((n : ℝ) * Real.pi * ((j : ℕ) : ℝ) / (N : ℝ)))
    (i : Fin (N + 1)) :
    (2 * u i - u (if (i : ℕ) = 0 then i + 1 else i - 1) -
        u (if (i : ℕ) = N then i - 1 else i + 1)) / (L / (N : ℝ)) ^ 2 =
      4 / (L / (N : ℝ)) ^ 2 * Real.sin ((n : ℝ) * Real.pi / (2 * (N : ℝ))) ^ 2 * u i
```

**In Lean.** `NeumannCosineHeadline.NeumannCosine.Discrete.Laplacian.discreteCosineMode_exhaustion` in [NeumannCosine/HeadlineChallenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/HeadlineChallenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem discreteCosineMode_exhaustion (L : ℝ) (N : ℕ) (hL : L ≠ 0) (hN : 0 < N)
    (u : Fin (N + 1) → ℝ) :
    ∃ c : Fin (N + 1) → ℝ,
      ∑ n : Fin (N + 1), c n • (fun j : Fin (N + 1) =>
        Real.cos (((n : ℕ) : ℝ) * Real.pi * ((j : ℕ) : ℝ) / (N : ℝ))) = u
```

**In Lean.** `NeumannCosineAudit.NeumannCosine.Discrete.Laplacian.discreteCosineModes_linearIndependent` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem discreteCosineModes_linearIndependent (L : ℝ) (N : ℕ) (hL : L ≠ 0) (hN : 0 < N) :
    LinearIndependent ℝ (fun n : Fin (N + 1) => fun j : Fin (N + 1) =>
      Real.cos (((n : ℕ) : ℝ) * Real.pi * ((j : ℕ) : ℝ) / (N : ℝ)))
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Discrete Neumann eigenvalues converge to the continuum ones

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For $L>0$ and fixed $n\ge1$,
\[\lim_{N\to\infty}\frac{4}{(L/N)^2}\sin^2\frac{n\pi}{2N}=\Big(\frac{n\pi}{L}\Big)^2.\]
```

**In Lean.** `NeumannCosineHeadline.NeumannCosine.Discrete.Eigenvalues.discreteNeumannEigenvalue_tendsto` in [NeumannCosine/HeadlineChallenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/HeadlineChallenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem discreteNeumannEigenvalue_tendsto (L : ℝ) (n : ℕ) (hL : 0 < L) (hn : 0 < n) :
    Tendsto (fun N : ℕ =>
        4 / (L / (N : ℝ)) ^ 2 * Real.sin ((n : ℝ) * Real.pi / (2 * (N : ℝ))) ^ 2)
      atTop (𝓝 (((n : ℝ) * Real.pi / L) ^ 2))
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Discrete modal minimum converges to the continuum infimum

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Let $L>0$, $K>0$ and $f:\mathbb R\to\mathbb R$ continuous at every $x>0$ with $Kx\le f(x)$ for $x>0$. With $\lambda_n^N=\frac{4}{(L/N)^2}\sin^2\frac{n\pi}{2N}$,
\[\lim_{N\to\infty}\ \min_{1\le n\le N}f(\lambda_n^N)=\inf_{n\ge1}f\Big(\Big(\frac{n\pi}{L}\Big)^2\Big).\]
```

**In Lean.** `NeumannCosineHeadline.NeumannCosine.Discrete.ModalMinimumLimit.discreteModalMin_tendsto` in [NeumannCosine/HeadlineChallenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/HeadlineChallenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem discreteModalMin_tendsto (f : ℝ → ℝ) (K L : ℝ) (hK : 0 < K) (hL : 0 < L)
    (hf : ∀ x : ℝ, 0 < x → ContinuousAt f x)
    (hlow : ∀ x : ℝ, 0 < x → K * x ≤ f x) :
    Tendsto (fun N : ℕ => sInf {y : ℝ | ∃ n : ℕ, 1 ≤ n ∧ n ≤ N ∧
        y = f (4 / (L / (N : ℝ)) ^ 2 * Real.sin ((n : ℝ) * Real.pi / (2 * (N : ℝ))) ^ 2)})
      atTop (𝓝 (sInf {y : ℝ | ∃ n : ℕ, 1 ≤ n ∧ y = f (((n : ℝ) * Real.pi / L) ^ 2)}))
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Normalized projections of the Neumann modes

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For $L>0$ and $j\in\mathbb Z$, $\int_0^L\cos\frac{j\pi y}{L}\,dy=L\,\mathbf 1_{j=0}$. For $n\ge1$, with $c_m(y)=\cos(m\pi y/L)$,
\[\frac2L\int_0^Lc_n^2=1,\qquad\frac2L\int_0^Lc_{3n}c_n=0,\qquad\frac2L\int_0^Lc_n^3c_n=\frac34.\]
```

**In Lean.** `NeumannCosineAudit.NeumannCosine.integral_cos_int_mul_pi_div` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem integral_cos_int_mul_pi_div (L : ℝ) (hL : 0 < L) (j : ℤ) :
    (∫ y in (0 : ℝ)..L,
      Real.cos (((j : ℝ) * Real.pi / L) * y)) =
        if j = 0 then L else 0
```

**In Lean.** `NeumannCosineAudit.NeumannCosine.normalized_integral_mode_mul_self` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem normalized_integral_mode_mul_self (L : ℝ) (n : ℕ) (hL : 0 < L) (hn : 0 < n) :
    2 / L * (∫ y in (0 : ℝ)..L,
      Real.cos ((n : ℝ) * Real.pi * y / L) * Real.cos ((n : ℝ) * Real.pi * y / L)) = 1
```

**In Lean.** `NeumannCosineAudit.NeumannCosine.normalized_integral_mode_three_mul` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem normalized_integral_mode_three_mul (L : ℝ) (n : ℕ) (hL : 0 < L) (hn : 0 < n) :
    2 / L * (∫ y in (0 : ℝ)..L,
      Real.cos (((3 * n : ℕ) : ℝ) * Real.pi * y / L) * Real.cos ((n : ℝ) * Real.pi * y / L)) = 0
```

**In Lean.** `NeumannCosineAudit.NeumannCosine.normalized_integral_mode_pow_four` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem normalized_integral_mode_pow_four (L : ℝ) (n : ℕ) (hL : 0 < L) (hn : 0 < n) :
    2 / L * (∫ y in (0 : ℝ)..L,
      Real.cos ((n : ℝ) * Real.pi * y / L) ^ 3 * Real.cos ((n : ℝ) * Real.pi * y / L)) = 3 / 4
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Closed forms of the three-cosine and cosine-sine kernels

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For $L>0$, $c_m(x)=\cos(m\pi x/L)$, $s_m(x)=\sin(m\pi x/L)$, index arithmetic in $\mathbb Z$: for $n,k\ge1$,
\[\int_0^Lc_is_ns_k=\frac L4\big(\mathbf 1_{i=|n-k|}-\mathbf 1_{i=n+k}+\mathbf 1_{n=k,\,i=0}\big);\]
for all $i,j,k$,
\[\int_0^Lc_ic_jc_k=\frac L4\big(\mathbf 1_{i-j=k}+\mathbf 1_{i-j=-k}+\mathbf 1_{i+j=k}\big)+\frac L4\mathbf 1_{i=j=k=0};\]
and for $n,k\ge1$, $\int_0^Lc_ic_js_ns_k=\frac L8\big(\mathbf 1_{i-j=n-k}+\mathbf 1_{i-j=k-n}+\mathbf 1_{i+j=n-k}+\mathbf 1_{i+j=k-n}-\mathbf 1_{i-j=n+k}-\mathbf 1_{i-j=-(n+k)}-\mathbf 1_{i+j=n+k}\big)$.
```

**In Lean.** `NeumannCosineAudit.NeumannCosine.KernelIntegrals.integral_cos_sin_sin` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem integral_cos_sin_sin (L : ℝ) (hL : 0 < L) (i n k : ℕ)
    (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (∫ x in (0 : ℝ)..L,
      Real.cos ((i : ℝ) * Real.pi * x / L) * Real.sin ((n : ℝ) * Real.pi * x / L) *
        Real.sin ((k : ℝ) * Real.pi * x / L)) =
      L / 4 * ((if i = Int.natAbs ((n : ℤ) - k) then 1 else 0) -
        (if i = n + k then 1 else 0) +
        (if n = k ∧ i = 0 then 1 else 0))
```

**In Lean.** `NeumannCosineAudit.NeumannCosine.KernelIntegrals.integral_cos_cos_cos` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem integral_cos_cos_cos (L : ℝ) (hL : 0 < L) (i j k : ℕ) :
    (∫ x in (0 : ℝ)..L,
      Real.cos ((i : ℝ) * Real.pi * x / L) * Real.cos ((j : ℝ) * Real.pi * x / L) *
        Real.cos ((k : ℝ) * Real.pi * x / L)) =
      L / 4 * ((if (i : ℤ) - j = k then 1 else 0) + (if (i : ℤ) - j = -k then 1 else 0) +
        (if (i : ℤ) + j = k then 1 else 0)) +
        L / 4 * (if k = 0 ∧ i = 0 ∧ j = 0 then 1 else 0)
```

**In Lean.** `NeumannCosineAudit.NeumannCosine.KernelIntegrals.integral_cos_cos_sin_sin` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem integral_cos_cos_sin_sin (L : ℝ) (hL : 0 < L) (i j n k : ℕ)
    (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (∫ x in (0 : ℝ)..L,
      Real.cos ((i : ℝ) * Real.pi * x / L) * Real.cos ((j : ℝ) * Real.pi * x / L) *
        Real.sin ((n : ℝ) * Real.pi * x / L) * Real.sin ((k : ℝ) * Real.pi * x / L)) =
      L / 8 * ((if (i : ℤ) - j = (n : ℤ) - k then 1 else 0) +
        (if (i : ℤ) - j = -((n : ℤ) - k) then 1 else 0) +
        (if (i : ℤ) + j = (n : ℤ) - k then 1 else 0) +
        (if (i : ℤ) + j = -((n : ℤ) - k) then 1 else 0) -
        (if (i : ℤ) - j = (n : ℤ) + k then 1 else 0) -
        (if (i : ℤ) - j = -((n : ℤ) + k) then 1 else 0) -
        (if (i : ℤ) + j = (n : ℤ) + k then 1 else 0))
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Product identities for absolutely summable cosine series

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For $L>0$ and absolutely summable $u,v,w$ (given either by $\sum|u_i|<\infty$ or as elements of $\ell^1(\mathbb N)$), with $c_m,s_m$ as above: for $n,k\ge1$,
\[\int_0^L\Big(\sum_iu_ic_i\Big)s_ns_k=\frac L4\big(u_{|n-k|}-u_{n+k}+\mathbf 1_{n=k}u_0\big);\]
for $k\ge0$,
\[\int_0^L\Big(\sum_iu_ic_i\Big)\Big(\sum_jv_jc_j\Big)c_k=\frac L4\Big(\sum_{i-j=k}+\sum_{i-j=-k}+\sum_{i+j=k}\Big)u_iv_j+\frac L4\mathbf 1_{k=0}u_0v_0;\]
and the two-sine and three-series identities of the headline rows hold with summability hypotheses in place of $\ell^1$ membership.
```

**In Lean.** `NeumannCosineAudit.NeumannCosine.ProductIdentities.cosine_sine_sine` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem cosine_sine_sine (L : ℝ) (hL : 0 < L) (u : ℕ → ℝ)
    (hu : Summable fun i => ‖u i‖) (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∫ x in (0 : ℝ)..L,
        (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
          Real.sin ((n : ℝ) * Real.pi * x / L) *
          Real.sin ((k : ℝ) * Real.pi * x / L) =
      L / 4 * (u (Int.natAbs ((n : ℤ) - k)) - u (n + k) +
        (if n = k then u 0 else 0))
```

**In Lean.** `NeumannCosineAudit.NeumannCosine.ProductIdentities.two_cosines_two_sines` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem two_cosines_two_sines (L : ℝ) (hL : 0 < L) (u v : ℕ → ℝ)
    (hu : Summable fun i => ‖u i‖) (hv : Summable fun j => ‖v j‖) (n k : ℕ)
    (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∫ x in (0 : ℝ)..L,
        (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
          (∑' j : ℕ, v j * Real.cos ((j : ℝ) * Real.pi * x / L)) *
          Real.sin ((n : ℝ) * Real.pi * x / L) *
          Real.sin ((k : ℝ) * Real.pi * x / L) =
      L / 8 *
        ((∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = (n : ℤ) - k},
            u p.1.1 * v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = -((n : ℤ) - k)},
            u p.1.1 * v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) + p.2 = (n : ℤ) - k},
            u p.1.1 * v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) + p.2 = -((n : ℤ) - k)},
            u p.1.1 * v p.1.2) -
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = (n : ℤ) + k},
            u p.1.1 * v p.1.2) -
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = -((n : ℤ) + k)},
            u p.1.1 * v p.1.2) -
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) + p.2 = (n : ℤ) + k},
            u p.1.1 * v p.1.2))
```

**In Lean.** `NeumannCosineAudit.NeumannCosine.ProductIdentities.cos_cos_cos` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem cos_cos_cos (L : ℝ) (hL : 0 < L) (u v : ℕ → ℝ)
    (hu : Summable fun i => ‖u i‖) (hv : Summable fun j => ‖v j‖) (k : ℕ) :
    ∫ x in (0 : ℝ)..L,
        (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
          (∑' j : ℕ, v j * Real.cos ((j : ℝ) * Real.pi * x / L)) *
          Real.cos ((k : ℝ) * Real.pi * x / L) =
      L / 4 * ((∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = k}, u p.1.1 * v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = -(k : ℤ)},
            u p.1.1 * v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) + p.2 = k}, u p.1.1 * v p.1.2)) +
        L / 4 * (if k = 0 then u 0 * v 0 else 0)
```

**In Lean.** `NeumannCosineAudit.NeumannCosine.ProductIdentities.cos_cos_cos_cos` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem cos_cos_cos_cos (L : ℝ) (hL : 0 < L) (u v w : ℕ → ℝ)
    (hu : Summable fun i => ‖u i‖) (hv : Summable fun j => ‖v j‖)
    (hw : Summable fun l => ‖w l‖) (k : ℕ) :
    ∫ x in (0 : ℝ)..L,
        (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
          (∑' j : ℕ, v j * Real.cos ((j : ℝ) * Real.pi * x / L)) *
          (∑' l : ℕ, w l * Real.cos ((l : ℝ) * Real.pi * x / L)) *
          Real.cos ((k : ℝ) * Real.pi * x / L) =
      L / 8 *
        ((∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) + t.2.1 + t.2.2 = k},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) + t.2.1 - t.2.2 = k},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) + t.2.1 - t.2.2 = -(k : ℤ)},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 + t.2.2 = k},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 + t.2.2 = -(k : ℤ)},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 - t.2.2 = k},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 - t.2.2 = -(k : ℤ)},
            u t.1.1 * v t.1.2.1 * w t.1.2.2)) +
        L / 8 * (if k = 0 then u 0 * v 0 * w 0 else 0)
```

**In Lean.** `NeumannCosineAudit.NeumannCosine.ProductIdentities.cosine_sine_sine_lp` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem cosine_sine_sine_lp (L : ℝ) (hL : 0 < L)
    (u : lp (fun _ : ℕ => ℝ) 1) (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∫ x in (0 : ℝ)..L,
        (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
          Real.sin ((n : ℝ) * Real.pi * x / L) *
          Real.sin ((k : ℝ) * Real.pi * x / L) =
      L / 4 * (u (Int.natAbs ((n : ℤ) - k)) - u (n + k) +
        (if n = k then u 0 else 0))
```

**In Lean.** `NeumannCosineAudit.NeumannCosine.ProductIdentities.cos_cos_cos_lp` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem cos_cos_cos_lp (L : ℝ) (hL : 0 < L) (u v : lp (fun _ : ℕ => ℝ) 1)
    (k : ℕ) :
    ∫ x in (0 : ℝ)..L,
        (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
          (∑' j : ℕ, v j * Real.cos ((j : ℝ) * Real.pi * x / L)) *
          Real.cos ((k : ℝ) * Real.pi * x / L) =
      L / 4 * ((∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = k}, u p.1.1 * v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = -(k : ℤ)},
            u p.1.1 * v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) + p.2 = k}, u p.1.1 * v p.1.2)) +
        L / 4 * (if k = 0 then u 0 * v 0 else 0)
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Termwise integration of a cosine series

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Let $\sum_n|u_n|<\infty$ and let $\kappa$ be continuous with $|\kappa|\le C$. Then for all $a,b,L\in\mathbb R$,
\[\sum_n\int_a^bu_n\cos\frac{n\pi x}{L}\,\kappa(x)\,dx=\int_a^b\sum_nu_n\cos\frac{n\pi x}{L}\,\kappa(x)\,dx,\]
the series on the left converging.
```

**In Lean.** `NeumannCosineAudit.NeumannCosine.Series.TermwiseIntegral.hasSum_intervalIntegral_cosine` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem hasSum_intervalIntegral_cosine (a b L : ℝ) (u : ℕ → ℝ)
    (kernel : ℝ → ℝ) (C : ℝ)
    (hu : Summable fun n => ‖u n‖)
    (hkernel_cont : Continuous kernel)
    (hkernel : ∀ x, ‖kernel x‖ ≤ C) (hC : 0 ≤ C) :
    HasSum
      (fun n : ℕ => ∫ x in a..b,
        u n * Real.cos ((n : ℝ) * Real.pi * x / L) * kernel x)
      (∫ x in a..b, ∑' n : ℕ,
        u n * Real.cos ((n : ℝ) * Real.pi * x / L) * kernel x)
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Quadratic decay of the cosine coefficients

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Under the hypotheses of the $W^{2,1}$ rows, with $w''=(w')'$ (which exists a.e. and is integrable), for $k\ge1$,
\[w_k=-\Big(\frac{L}{k\pi}\Big)^2\frac2L\int_0^Lw''(x)\cos\frac{k\pi x}{L}\,dx,\qquad|w_k|\le\frac{2L}{\pi^2}\Big(\int_0^L|w''|\Big)\frac1{k^2}.\]
```

**In Lean.** `NeumannCosineAudit.NeumannCosine.Coefficients.cosineCoeff_eq_neg_mul_secondDeriv` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem cosineCoeff_eq_neg_mul_secondDeriv (L : ℝ) (hL : 0 < L) {w w' : ℝ → ℝ}
    (hac : AbsolutelyContinuousOnInterval w 0 L)
    (hderiv : ∀ x ∈ Ioo 0 L, HasDerivAt w (w' x) x)
    (hac' : AbsolutelyContinuousOnInterval w' 0 L)
    (hleft : w' 0 = 0) (hright : w' L = 0) {k : ℕ} (hk : k ≠ 0) :
    (if k = 0 then 1 / L else 2 / L) *
        ∫ x in (0 : ℝ)..L, w x * Real.cos ((k : ℝ) * Real.pi * x / L) =
      -(L / ((k : ℝ) * Real.pi)) ^ 2 *
        (2 / L * ∫ x in (0 : ℝ)..L,
          deriv w' x * Real.cos ((k : ℝ) * Real.pi * x / L))
```

**In Lean.** `NeumannCosineAudit.NeumannCosine.Coefficients.abs_cosineCoeff_le` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem abs_cosineCoeff_le (L : ℝ) (hL : 0 < L) {w w' : ℝ → ℝ}
    (hac : AbsolutelyContinuousOnInterval w 0 L)
    (hderiv : ∀ x ∈ Ioo 0 L, HasDerivAt w (w' x) x)
    (hac' : AbsolutelyContinuousOnInterval w' 0 L)
    (hleft : w' 0 = 0) (hright : w' L = 0) {k : ℕ} (hk : k ≠ 0) :
    |(if k = 0 then 1 / L else 2 / L) *
        ∫ x in (0 : ℝ)..L, w x * Real.cos ((k : ℝ) * Real.pi * x / L)| ≤
      2 * L / Real.pi ^ 2 * (∫ x in (0 : ℝ)..L, |deriv w' x|) *
        (1 / (k : ℝ) ^ 2)
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Summable cosine coefficients of H^2 functions with Neumann trace

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Under the hypotheses of the $H^2$ row, $\sum_{k\ge0}|w_k|<\infty$.
```

**In Lean.** `NeumannCosineAudit.NeumannCosine.Sobolev.H2Neumann.H2.summable_norm_cosineCoeff` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem H2.summable_norm_cosineCoeff {L : ℝ} (hL : 0 < L) {w w₁ w₂ : ℝ → ℝ}
    (hw : MemLp w 2 (volume.restrict (Ioo 0 L)))
    (hw₁ : MemLp w₁ 2 (volume.restrict (Ioo 0 L)))
    (hw₂ : MemLp w₂ 2 (volume.restrict (Ioo 0 L)))
    (hd₁ : ∀ φ : ℝ → ℝ, (ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ioo 0 L) →
      ∫ x in (0 : ℝ)..L, w x * deriv φ x = -∫ x in (0 : ℝ)..L, w₁ x * φ x)
    (hd₂ : ∀ φ : ℝ → ℝ, (ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ioo 0 L) →
      ∫ x in (0 : ℝ)..L, w₁ x * deriv φ x = -∫ x in (0 : ℝ)..L, w₂ x * φ x)
    (hN : ∃ V : ℝ → ℝ, ContinuousOn V (Icc 0 L) ∧ (∀ᵐ x, x ∈ Ioo 0 L → w₁ x = V x) ∧
      V 0 = 0 ∧ V L = 0) :
    Summable fun k : ℕ =>
      ‖(if k = 0 then 1 / L else 2 / L) *
        ∫ x in (0 : ℝ)..L, w x * Real.cos ((k : ℝ) * Real.pi * x / L)‖
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Cosine projection of a divergence-form source

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Let $L>0$, $k\in\mathbb N$, $R_0\in L^1(0,L)$ and $R_1$ with $R_1(0)=R_1(L)=0$, where either $R_1$ is continuous on $[0,L]$, differentiable at every point of $(0,L)$, with interval-integrable derivative $R_1'$, or $R_1$ is absolutely continuous on $[0,L]$. If $|R_0|,|R_1|\le B$ on $[0,L]$, then
\[\Big|\int_0^L\big(R_0(x)+R_1'(x)\big)\cos\frac{k\pi x}{L}\,dx\Big|\le(L+k\pi)B.\]
```

**In Lean.** `NeumannCosineAudit.NeumannCosine.DivergenceFormProjection.abs_integral_source_add_deriv_mul_cos_le` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem abs_integral_source_add_deriv_mul_cos_le {L B : ℝ} (hL : 0 < L) (k : ℕ) {R0 R1 dR1 : ℝ → ℝ}
    (hR0 : IntervalIntegrable R0 volume 0 L)
    (hR1c : ContinuousOn R1 (Icc 0 L)) (hR1d : ∀ x ∈ Ioo 0 L, HasDerivAt R1 (dR1 x) x)
    (hdR1 : IntervalIntegrable dR1 volume 0 L) (h0 : R1 0 = 0) (hL0 : R1 L = 0)
    (hB0 : ∀ x ∈ Icc 0 L, |R0 x| ≤ B) (hB1 : ∀ x ∈ Icc 0 L, |R1 x| ≤ B) :
    |∫ x in (0 : ℝ)..L, (R0 x + dR1 x) * cos (k * π * x / L)| ≤ (L + k * π) * B
```

**In Lean.** `NeumannCosineAudit.NeumannCosine.DivergenceFormProjection.abs_integral_source_add_deriv_mul_cos_le_of_absolutelyContinuous` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem abs_integral_source_add_deriv_mul_cos_le_of_absolutelyContinuous {L B : ℝ} (hL : 0 < L) (k : ℕ)
    {R0 R1 : ℝ → ℝ} (hR0 : IntervalIntegrable R0 volume 0 L)
    (hR1 : AbsolutelyContinuousOnInterval R1 0 L) (h0 : R1 0 = 0) (hL0 : R1 L = 0)
    (hB0 : ∀ x ∈ Icc 0 L, |R0 x| ≤ B) (hB1 : ∀ x ∈ Icc 0 L, |R1 x| ≤ B) :
    |∫ x in (0 : ℝ)..L, (R0 x + deriv R1 x) * cos (k * π * x / L)| ≤ (L + k * π) * B
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Discrete Neumann eigenvalues: sinc form, ordering and lower bound

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Let $\lambda_n^N=\frac{4}{(L/N)^2}\sin^2\frac{n\pi}{2N}$ and $N\ge1$. If $L\neq0$ and $n\ge1$, then $\lambda_n^N=(n\pi/L)^2\operatorname{sinc}^2\frac{n\pi}{2N}$; if $L\neq0$ and $n<k\le N$, then $\lambda_n^N<\lambda_k^N$; if $L>0$ and $1\le n\le N$, then $\lambda_1^N\le\lambda_n^N$; and if $L>0$ and $n\le N$, then $\lambda_n^N\ge4n^2/L^2$.
```

**In Lean.** `NeumannCosineAudit.NeumannCosine.Discrete.Eigenvalues.discreteNeumannEigenvalue_eq_mul_sinc_sq` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem discreteNeumannEigenvalue_eq_mul_sinc_sq (L : ℝ) (n N : ℕ)
    (hL : L ≠ 0) (hn : 0 < n) (hN : 0 < N) :
    4 / (L / (N : ℝ)) ^ 2 * Real.sin ((n : ℝ) * Real.pi / (2 * (N : ℝ))) ^ 2 =
      ((n : ℝ) * Real.pi / L) ^ 2 * Real.sinc ((n : ℝ) * Real.pi / (2 * (N : ℝ))) ^ 2
```

**In Lean.** `NeumannCosineAudit.NeumannCosine.Discrete.Eigenvalues.discreteNeumannEigenvalue_one_le` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem discreteNeumannEigenvalue_one_le (L : ℝ) (n N : ℕ)
    (hL : 0 < L) (hN : 0 < N) (hn : 1 ≤ n) (hnN : n ≤ N) :
    4 / (L / (N : ℝ)) ^ 2 * Real.sin (((1 : ℕ) : ℝ) * Real.pi / (2 * (N : ℝ))) ^ 2 ≤
      4 / (L / (N : ℝ)) ^ 2 * Real.sin ((n : ℝ) * Real.pi / (2 * (N : ℝ))) ^ 2
```

**In Lean.** `NeumannCosineAudit.NeumannCosine.Discrete.Eigenvalues.discreteNeumannEigenvalue_lower_bound` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem discreteNeumannEigenvalue_lower_bound (L : ℝ) (n N : ℕ)
    (hL : 0 < L) (hN : 0 < N) (hnN : n ≤ N) :
    4 * (n : ℝ) ^ 2 / L ^ 2 ≤ 4 / (L / (N : ℝ)) ^ 2 * Real.sin ((n : ℝ) * Real.pi / (2 * (N : ℝ))) ^ 2
```

**In Lean.** `NeumannCosineAudit.NeumannCosine.Discrete.Laplacian.discreteNeumannEigenvalue_lt_of_lt` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem discreteNeumannEigenvalue_lt_of_lt (L : ℝ) (N n k : ℕ) (hL : L ≠ 0) (hN : 0 < N)
    (hnk : n < k) (hkN : k ≤ N) :
    4 / (L / (N : ℝ)) ^ 2 * Real.sin ((n : ℝ) * Real.pi / (2 * (N : ℝ))) ^ 2 <
      4 / (L / (N : ℝ)) ^ 2 * Real.sin ((k : ℝ) * Real.pi / (2 * (N : ℝ))) ^ 2
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

## What the checks establish

- **Every proof is checked by Lean.** The package builds; no `sorry` (an unfinished proof) remains; the only axioms used are `Classical.choice`, `Quot.sound`, `propext` (allowed: `propext`, `Quot.sound`, `Classical.choice`).
- **The statements shown are the ones proved.** For 50 statement(s), a second checker (comparator) confirmed that the proof proves exactly the statement shown, with only the permitted axioms, and independent Lean kernels replayed the proof.
- **Not checked by any tool:** that a title or note describes its Lean statement. A definition listed under *Definitions checked by a person* is compared by name and type only.

The full account of what each check covers and what it takes on trust is lean-pkg's [trust model](https://github.com/lean-pkg/lean-pkg/blob/main/docs/trust-model.md).

## How this was checked

- lean-pkg's claims ledger: **ready**, every required claim is closed by the recorded receipts; 37 of 37 required claim(s) verified (`sha256:0d19b11488fb5018…`).
- Build check (`lean-pkg gate`) at commit `d16a23572ff3`: `sorry` count 0; axioms used: `Classical.choice`, `Quot.sound`, `propext`.
- Statement comparison (comparator) at commit `d16a23572ff3`: 2 configuration(s), 50 theorem(s) compared (each Challenge statement against its Solution proof); permitted axioms: `Classical.choice`, `Quot.sound`, `propext`; definitions compared by name only: none.

### Receipts

| Receipt | Check | Commit | Date | Job | SHA-256 |
|---|---|---|---|---|---|
| `.lean-receipts/067501d7208c-comparator.json` | statement comparison | `067501d7208c` | 2026-10-19 | — | `5b8436270bc250f695edf2f13e97eefa848376bce725d83ed290b52106209321` |
| `.lean-receipts/067501d7208c-slurm-5586731.json` | build | `067501d7208c` | 2026-10-19 | slurm-5586731 | `85cf8579bd4ebe1d53944c36ee5ab85da7d1353274cff8894ac42aace8bfbe51` |
| `.lean-receipts/067501d7208c-slurm-5586732.json` | build | `067501d7208c` | 2026-10-19 | slurm-5586732 | `b85eeed33282a6628c3037f22267ef7eb15bcc381a181e5035c51c04e698736e` |
| `.lean-receipts/d16a23572ff3-comparator.json` (used here) | statement comparison | `d16a23572ff3` | 2026-10-20 | — | `061fc14a7dd9bec9affd0f4627d886543072545f5246ef6e0806e89954a76414` |
| `.lean-receipts/d16a23572ff3-slurm-5587231.json` (used here) | build | `d16a23572ff3` | 2026-10-20 | slurm-5587231 | `f614ce7a071d6417e8c6b59fcf5a9aa4b284aecd4080326580364d67b14c0fdf` |

*(used here)*: the receipt the lean-pkg registry holds for this package, which the lines above read. SHA-256 is of the file as committed.

### Reproduce

- Lean toolchain: `leanprover/lean4:v4.35.0`.
- Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679` (lake-manifest.json).

```bash
git clone https://github.com/chenle02/neumann-cosine-lean
cd neumann-cosine-lean
git checkout d16a23572ff3212856109dda2010668ed7adbf73   # the commit the build check binds
lake exe cache get
lake build
```

Expected: `#print axioms` on any declaration above reports a subset of {`Classical.choice`, `Quot.sound`, `propext`} (the union the build check records); `sorryAx` never appears.

## Citation

Le Chen. *NeumannCosine: Neumann cosine series on an interval and the discrete Neumann Laplacian in Lean 4*. Version 0.1.0.

See [CITATION.cff](CITATION.cff).

## License

Released under `Apache-2.0`; see [LICENSE](LICENSE).

## Acknowledgments

Developed and verified with [lean-pkg](https://github.com/lean-pkg/lean-pkg) ([doi:10.5281/zenodo.23272098](https://doi.org/10.5281/zenodo.23272098)).
This work was completed in part with resources provided by the [Auburn University Easley Cluster](https://hpc.auburn.edu/hpc/docs/hpcdocs/build/html/easley/intro.html).

<!-- lean-pkg:page:end -->
