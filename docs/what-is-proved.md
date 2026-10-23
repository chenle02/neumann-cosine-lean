# What is proved

This guide presents the existing `neumann-cosine-lean` results with their exact compared Lean statements.
The proofs are classical mathematics. Their application to a particular differential equation requires
checking that equation's hypotheses separately.

## Notation and scope

The interval has length `L > 0`; the mode of index `k` is `cos(k*pi*x/L)`. The zero coefficient is the mean; positive coefficients use the factor `2/L`. Regularity, trace, summability and discrete-grid assumptions vary by result and are retained in each statement below.

| Result | Evidence |
|---|---|
| Orthogonality and Gram values of the Neumann cosine modes | Compared statement; existing release receipts |
| Closed form of the integral of four cosine modes | Compared statement; existing release receipts |
| Integral of a product of three cosine series against a cosine | Compared statement; existing release receipts |
| Integral of two cosine series against two sines | Compared statement; existing release receipts |
| Cosine coefficients of W^{2,1} Neumann functions are absolutely summable | Compared statement; existing release receipts |
| Pointwise cosine expansion of W^{2,1} Neumann functions | Compared statement; existing release receipts |
| The du Bois-Reymond lemma on an interval | Compared statement; existing release receipts |
| W^{1,1} functions have an absolutely continuous representative | Compared statement; existing release receipts |
| Cosine expansion of H^2 functions with Neumann trace | Compared statement; existing release receipts |
| Cosine eigenbasis of the discrete Neumann Laplacian | Compared statement; existing release receipts |
| Discrete Neumann eigenvalues converge to the continuum ones | Compared statement; existing release receipts |
| Discrete modal minimum converges to the continuum infimum | Compared statement; existing release receipts |
| Normalized projections of the Neumann modes | Compared statement; existing release receipts |
| Closed forms of the three-cosine and cosine-sine kernels | Compared statement; existing release receipts |
| Product identities for absolutely summable cosine series | Compared statement; existing release receipts |
| Termwise integration of a cosine series | Compared statement; existing release receipts |
| Quadratic decay of the cosine coefficients | Compared statement; existing release receipts |
| Summable cosine coefficients of H^2 functions with Neumann trace | Compared statement; existing release receipts |
| Cosine projection of a divergence-form source | Compared statement; existing release receipts |
| Discrete Neumann eigenvalues: sinc form, ordering and lower bound | Compared statement; existing release receipts |

## Results

### Orthogonality and Gram values of the Neumann cosine modes

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

For $`L>0`$ and $`m,n\in\mathbb N`$,


```math
\int_0^L \cos\frac{m\pi y}{L}\cos\frac{n\pi y}{L}\,dy=\begin{cases}L,& m=n=0,\\ L/2,& m=n\neq 0,\\ 0,& m\neq n.\end{cases}
```


**Lean.** `NeumannCosineHeadline.NeumannCosine.integral_mode_mul_mode` in [NeumannCosine/HeadlineChallenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/HeadlineChallenge.lean#L41): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem integral_mode_mul_mode (L : ℝ) (hL : 0 < L) (m n : ℕ) :
    (∫ y in (0 : ℝ)..L,
      Real.cos ((m : ℝ) * Real.pi * y / L) * Real.cos ((n : ℝ) * Real.pi * y / L)) =
      if m = n then (if m = 0 then L else L / 2) else 0
```

</details>


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `d16a23572ff3212856109dda2010668ed7adbf73` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

### Closed form of the integral of four cosine modes

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

For $`L>0`$, $`i,j,l,k\in\mathbb N`$ and $`c_m(x)=\cos(m\pi x/L)`$,


```math
\int_0^L c_i c_j c_l c_k\,dx=\frac L8\Big(\mathbf 1_{i+j+l=k}+\mathbf 1_{i+j-l=k}+\mathbf 1_{i+j-l=-k}+\mathbf 1_{i-j+l=k}+\mathbf 1_{i-j+l=-k}+\mathbf 1_{i-j-l=k}+\mathbf 1_{i-j-l=-k}\Big)+\frac L8\,\mathbf 1_{i=j=l=k=0},
```


with the index arithmetic in $`\mathbb Z`$.


**Lean.** `NeumannCosineHeadline.NeumannCosine.KernelIntegrals.integral_cos_cos_cos_cos` in [NeumannCosine/HeadlineChallenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/HeadlineChallenge.lean#L59): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `d16a23572ff3212856109dda2010668ed7adbf73` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

### Integral of a product of three cosine series against a cosine

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

For $`L>0`$, $`u,v,w\in\ell^1(\mathbb N)`$ and $`k\in\mathbb N`$,


```math
\int_0^L\Big(\sum_i u_i c_i\Big)\Big(\sum_j v_j c_j\Big)\Big(\sum_l w_l c_l\Big)c_k\,dx=\frac L8\sum_{\sigma}\ \sum_{i+\sigma_1 j+\sigma_2 l=\sigma_3 k}u_iv_jw_l+\frac L8\,\mathbf 1_{k=0}\,u_0v_0w_0,
```


where $`c_m(x)=\cos(m\pi x/L)`$ and $`\sigma=(\sigma_1,\sigma_2,\sigma_3)`$ runs over the seven sign patterns $`(+,+,+)`$, $`(+,-,\pm)`$, $`(-,+,\pm)`$, $`(-,-,\pm)`$; each inner sum is over $`(i,j,l)\in\mathbb N^3`$ with the constraint in $`\mathbb Z`$.


**Lean.** `NeumannCosineHeadline.NeumannCosine.ProductIdentities.cos_cos_cos_cos_lp` in [NeumannCosine/HeadlineChallenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/HeadlineChallenge.lean#L85): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `d16a23572ff3212856109dda2010668ed7adbf73` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

### Integral of two cosine series against two sines

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

For $`L>0`$, $`u,v\in\ell^1(\mathbb N)`$ and $`n,k\ge 1`$, with $`c_m(x)=\cos(m\pi x/L)`$ and $`s_m(x)=\sin(m\pi x/L)`$,


```math
\int_0^L\Big(\sum_i u_ic_i\Big)\Big(\sum_j v_jc_j\Big)s_ns_k\,dx=\frac L8\Big(\sum_{i-j=n-k}+\sum_{i-j=k-n}+\sum_{i+j=n-k}+\sum_{i+j=k-n}-\sum_{i-j=n+k}-\sum_{i-j=-(n+k)}-\sum_{i+j=n+k}\Big)u_iv_j,
```


each sum over $`(i,j)\in\mathbb N^2`$ with the constraint in $`\mathbb Z`$.


**Lean.** `NeumannCosineHeadline.NeumannCosine.ProductIdentities.two_cosines_two_sines_lp` in [NeumannCosine/HeadlineChallenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/HeadlineChallenge.lean#L116): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `d16a23572ff3212856109dda2010668ed7adbf73` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

### Cosine coefficients of W^{2,1} Neumann functions are absolutely summable

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

Let $`L>0`$ and let $`w`$ be absolutely continuous on $`[0,L]`$ with derivative $`w'(x)`$ at every $`x\in(0,L)`$, where $`w'`$ is absolutely continuous on $`[0,L]`$ and $`w'(0)=w'(L)=0`$. With $`w_0=\frac1L\int_0^Lw`$ and $`w_k=\frac2L\int_0^Lw(x)\cos\frac{k\pi x}{L}\,dx`$ for $`k\ge1`$,


```math
\sum_{k\ge0}|w_k|<\infty.
```


**Lean.** `NeumannCosineHeadline.NeumannCosine.Coefficients.summable_norm_cosineCoeff` in [NeumannCosine/HeadlineChallenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/HeadlineChallenge.lean#L154): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `d16a23572ff3212856109dda2010668ed7adbf73` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

### Pointwise cosine expansion of W^{2,1} Neumann functions

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

Under the hypotheses of the previous row, for every $`x\in[0,L]`$,


```math
w(x)=\sum_{k\ge0}w_k\cos\frac{k\pi x}{L},
```


the series converging absolutely.


**Lean.** `NeumannCosineHeadline.NeumannCosine.Coefficients.hasSum_cosineCoeff` in [NeumannCosine/HeadlineChallenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/HeadlineChallenge.lean#L169): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `d16a23572ff3212856109dda2010668ed7adbf73` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

### The du Bois-Reymond lemma on an interval

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

Let $`L>0`$ and $`h\in L^1(0,L)`$. If $`\int_0^L h\,\varphi'\,dx=0`$ for every $`\varphi\in C_c^\infty(0,L)`$ (smooth, compactly supported, $`\operatorname{tsupp}\varphi\subseteq(0,L)`$), then there is $`c\in\mathbb R`$ with $`h=c`$ almost everywhere on $`(0,L)`$.


**Lean.** `NeumannCosineHeadline.NeumannCosine.Sobolev.WeakDerivative.ae_eq_const_of_integral_mul_deriv_eq_zero` in [NeumannCosine/HeadlineChallenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/HeadlineChallenge.lean#L192): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem ae_eq_const_of_integral_mul_deriv_eq_zero {L : ℝ} (hL : 0 < L) {h : ℝ → ℝ}
    (hh : IntervalIntegrable h volume 0 L)
    (H : ∀ φ : ℝ → ℝ, (ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ioo 0 L) →
      ∫ x in (0 : ℝ)..L, h x * deriv φ x = 0) :
    ∃ c : ℝ, ∀ᵐ x, x ∈ Ioo 0 L → h x = c
```

</details>


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `d16a23572ff3212856109dda2010668ed7adbf73` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

### W^{1,1} functions have an absolutely continuous representative

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

Let $`L>0`$ and $`w,g\in L^1(0,L)`$ with $`\int_0^Lw\,\varphi'\,dx=-\int_0^Lg\,\varphi\,dx`$ for every $`\varphi\in C_c^\infty(0,L)`$. Then for some $`c\in\mathbb R`$ the function $`W(x)=c+\int_0^xg(t)\,dt`$ satisfies $`w=W`$ a.e. on $`(0,L)`$, $`W`$ is absolutely continuous on $`[0,L]`$, and $`W'(x)=g(x)`$ for almost every $`x\in[0,L]`$.


**Lean.** `NeumannCosineHeadline.NeumannCosine.Sobolev.WeakDerivative.HasWeakDeriv.ae_eq_primitive` in [NeumannCosine/HeadlineChallenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/HeadlineChallenge.lean#L207): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem HasWeakDeriv.ae_eq_primitive {L : ℝ} (hL : 0 < L) {w g : ℝ → ℝ}
    (hw : IntervalIntegrable w volume 0 L) (hg : IntervalIntegrable g volume 0 L)
    (hwg : ∀ φ : ℝ → ℝ, (ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ioo 0 L) →
      ∫ x in (0 : ℝ)..L, w x * deriv φ x = -∫ x in (0 : ℝ)..L, g x * φ x) :
    ∃ c : ℝ, (∀ᵐ x, x ∈ Ioo 0 L → w x = c + ∫ t in (0 : ℝ)..x, g t) ∧
      AbsolutelyContinuousOnInterval (fun x => c + ∫ t in (0 : ℝ)..x, g t) 0 L ∧
      ∀ᵐ x, x ∈ Icc 0 L → HasDerivAt (fun x => c + ∫ t in (0 : ℝ)..x, g t) (g x) x
```

</details>


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `d16a23572ff3212856109dda2010668ed7adbf73` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

### Cosine expansion of H^2 functions with Neumann trace

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

Let $`L>0`$ and $`w,w_1,w_2\in L^2(0,L)`$, with $`w_1`$ the weak derivative of $`w`$ and $`w_2`$ the weak derivative of $`w_1`$ (tested against $`C_c^\infty(0,L)`$). Suppose some $`V`$ continuous on $`[0,L]`$ equals $`w_1`$ a.e. on $`(0,L)`$ and $`V(0)=V(L)=0`$. Then there is $`W`$ continuous on $`[0,L]`$ with $`W=w`$ a.e. on $`(0,L)`$ and, for every $`x\in[0,L]`$,


```math
W(x)=\sum_{k\ge0}w_k\cos\frac{k\pi x}{L},
```


where $`w_k`$ are the cosine coefficients of $`w`$ (as above).


**Lean.** `NeumannCosineHeadline.NeumannCosine.Sobolev.H2Neumann.H2.hasSum_cosineCoeff` in [NeumannCosine/HeadlineChallenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/HeadlineChallenge.lean#L232): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `d16a23572ff3212856109dda2010668ed7adbf73` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

### Cosine eigenbasis of the discrete Neumann Laplacian

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

Let $`L\neq0`$, $`N\ge1`$, $`h=L/N`$, and on the grid $`\{0,\dots,N\}`$ let $`(\Delta_h u)_i=(2u_i-u_{i-1}-u_{i+1})/h^2`$ with reflected ghost points $`u_{-1}=u_1`$, $`u_{N+1}=u_{N-1}`$. For $`0\le n\le N`$ the vector $`u_j=\cos(n\pi j/N)`$ satisfies


```math
\Delta_h u=\frac{4}{h^2}\sin^2\frac{n\pi}{2N}\,u,
```


these $`N+1`$ cosine vectors are linearly independent, and every real function on the grid is a linear combination of them.


**Lean.** `NeumannCosineHeadline.NeumannCosine.Discrete.Laplacian.reflectedNegLaplacian_cosine_eigenpair` in [NeumannCosine/HeadlineChallenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/HeadlineChallenge.lean#L267): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem reflectedNegLaplacian_cosine_eigenpair (L : ℝ) (N n : ℕ) (hL : L ≠ 0)
    (hN : 0 < N) (hnN : n ≤ N) (u : Fin (N + 1) → ℝ)
    (hu : ∀ j : Fin (N + 1), u j = Real.cos ((n : ℝ) * Real.pi * ((j : ℕ) : ℝ) / (N : ℝ)))
    (i : Fin (N + 1)) :
    (2 * u i - u (if (i : ℕ) = 0 then i + 1 else i - 1) -
        u (if (i : ℕ) = N then i - 1 else i + 1)) / (L / (N : ℝ)) ^ 2 =
      4 / (L / (N : ℝ)) ^ 2 * Real.sin ((n : ℝ) * Real.pi / (2 * (N : ℝ))) ^ 2 * u i
```

</details>

**Lean.** `NeumannCosineHeadline.NeumannCosine.Discrete.Laplacian.discreteCosineMode_exhaustion` in [NeumannCosine/HeadlineChallenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/HeadlineChallenge.lean#L283): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem discreteCosineMode_exhaustion (L : ℝ) (N : ℕ) (hL : L ≠ 0) (hN : 0 < N)
    (u : Fin (N + 1) → ℝ) :
    ∃ c : Fin (N + 1) → ℝ,
      ∑ n : Fin (N + 1), c n • (fun j : Fin (N + 1) =>
        Real.cos (((n : ℕ) : ℝ) * Real.pi * ((j : ℕ) : ℝ) / (N : ℝ))) = u
```

</details>

**Lean.** `NeumannCosineAudit.NeumannCosine.Discrete.Laplacian.discreteCosineModes_linearIndependent` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean#L700): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem discreteCosineModes_linearIndependent (L : ℝ) (N : ℕ) (hL : L ≠ 0) (hN : 0 < N) :
    LinearIndependent ℝ (fun n : Fin (N + 1) => fun j : Fin (N + 1) =>
      Real.cos (((n : ℕ) : ℝ) * Real.pi * ((j : ℕ) : ℝ) / (N : ℝ)))
```

</details>


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `d16a23572ff3212856109dda2010668ed7adbf73` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

### Discrete Neumann eigenvalues converge to the continuum ones

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

For $`L>0`$ and fixed $`n\ge1`$,


```math
\lim_{N\to\infty}\frac{4}{(L/N)^2}\sin^2\frac{n\pi}{2N}=\Big(\frac{n\pi}{L}\Big)^2.
```


**Lean.** `NeumannCosineHeadline.NeumannCosine.Discrete.Eigenvalues.discreteNeumannEigenvalue_tendsto` in [NeumannCosine/HeadlineChallenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/HeadlineChallenge.lean#L301): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem discreteNeumannEigenvalue_tendsto (L : ℝ) (n : ℕ) (hL : 0 < L) (hn : 0 < n) :
    Tendsto (fun N : ℕ =>
        4 / (L / (N : ℝ)) ^ 2 * Real.sin ((n : ℝ) * Real.pi / (2 * (N : ℝ))) ^ 2)
      atTop (𝓝 (((n : ℝ) * Real.pi / L) ^ 2))
```

</details>


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `d16a23572ff3212856109dda2010668ed7adbf73` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

### Discrete modal minimum converges to the continuum infimum

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

Let $`L>0`$, $`K>0`$ and $`f:\mathbb R\to\mathbb R`$ continuous at every $`x>0`$ with $`Kx\le f(x)`$ for $`x>0`$. With $`\lambda_n^N=\frac{4}{(L/N)^2}\sin^2\frac{n\pi}{2N}`$,


```math
\lim_{N\to\infty}\ \min_{1\le n\le N}f(\lambda_n^N)=\inf_{n\ge1}f\Big(\Big(\frac{n\pi}{L}\Big)^2\Big).
```


**Lean.** `NeumannCosineHeadline.NeumannCosine.Discrete.ModalMinimumLimit.discreteModalMin_tendsto` in [NeumannCosine/HeadlineChallenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/HeadlineChallenge.lean#L322): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem discreteModalMin_tendsto (f : ℝ → ℝ) (K L : ℝ) (hK : 0 < K) (hL : 0 < L)
    (hf : ∀ x : ℝ, 0 < x → ContinuousAt f x)
    (hlow : ∀ x : ℝ, 0 < x → K * x ≤ f x) :
    Tendsto (fun N : ℕ => sInf {y : ℝ | ∃ n : ℕ, 1 ≤ n ∧ n ≤ N ∧
        y = f (4 / (L / (N : ℝ)) ^ 2 * Real.sin ((n : ℝ) * Real.pi / (2 * (N : ℝ))) ^ 2)})
      atTop (𝓝 (sInf {y : ℝ | ∃ n : ℕ, 1 ≤ n ∧ y = f (((n : ℝ) * Real.pi / L) ^ 2)}))
```

</details>


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `d16a23572ff3212856109dda2010668ed7adbf73` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

### Normalized projections of the Neumann modes

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

For $`L>0`$ and $`j\in\mathbb Z`$, $`\int_0^L\cos\frac{j\pi y}{L}\,dy=L\,\mathbf 1_{j=0}`$. For $`n\ge1`$, with $`c_m(y)=\cos(m\pi y/L)`$,


```math
\frac2L\int_0^Lc_n^2=1,\qquad\frac2L\int_0^Lc_{3n}c_n=0,\qquad\frac2L\int_0^Lc_n^3c_n=\frac34.
```


**Lean.** `NeumannCosineAudit.NeumannCosine.integral_cos_int_mul_pi_div` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean#L342): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem integral_cos_int_mul_pi_div (L : ℝ) (hL : 0 < L) (j : ℤ) :
    (∫ y in (0 : ℝ)..L,
      Real.cos (((j : ℝ) * Real.pi / L) * y)) =
        if j = 0 then L else 0
```

</details>

**Lean.** `NeumannCosineAudit.NeumannCosine.normalized_integral_mode_mul_self` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean#L351): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem normalized_integral_mode_mul_self (L : ℝ) (n : ℕ) (hL : 0 < L) (hn : 0 < n) :
    2 / L * (∫ y in (0 : ℝ)..L,
      Real.cos ((n : ℝ) * Real.pi * y / L) * Real.cos ((n : ℝ) * Real.pi * y / L)) = 1
```

</details>

**Lean.** `NeumannCosineAudit.NeumannCosine.normalized_integral_mode_three_mul` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean#L359): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem normalized_integral_mode_three_mul (L : ℝ) (n : ℕ) (hL : 0 < L) (hn : 0 < n) :
    2 / L * (∫ y in (0 : ℝ)..L,
      Real.cos (((3 * n : ℕ) : ℝ) * Real.pi * y / L) * Real.cos ((n : ℝ) * Real.pi * y / L)) = 0
```

</details>

**Lean.** `NeumannCosineAudit.NeumannCosine.normalized_integral_mode_pow_four` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean#L367): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem normalized_integral_mode_pow_four (L : ℝ) (n : ℕ) (hL : 0 < L) (hn : 0 < n) :
    2 / L * (∫ y in (0 : ℝ)..L,
      Real.cos ((n : ℝ) * Real.pi * y / L) ^ 3 * Real.cos ((n : ℝ) * Real.pi * y / L)) = 3 / 4
```

</details>


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `d16a23572ff3212856109dda2010668ed7adbf73` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

### Closed forms of the three-cosine and cosine-sine kernels

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

For $`L>0`$, $`c_m(x)=\cos(m\pi x/L)`$, $`s_m(x)=\sin(m\pi x/L)`$, index arithmetic in $`\mathbb Z`$: for $`n,k\ge1`$,


```math
\int_0^Lc_is_ns_k=\frac L4\big(\mathbf 1_{i=|n-k|}-\mathbf 1_{i=n+k}+\mathbf 1_{n=k,\,i=0}\big);
```


for all $`i,j,k`$,


```math
\int_0^Lc_ic_jc_k=\frac L4\big(\mathbf 1_{i-j=k}+\mathbf 1_{i-j=-k}+\mathbf 1_{i+j=k}\big)+\frac L4\mathbf 1_{i=j=k=0};
```


and for $`n,k\ge1`$, $`\int_0^Lc_ic_js_ns_k=\frac L8\big(\mathbf 1_{i-j=n-k}+\mathbf 1_{i-j=k-n}+\mathbf 1_{i+j=n-k}+\mathbf 1_{i+j=k-n}-\mathbf 1_{i-j=n+k}-\mathbf 1_{i-j=-(n+k)}-\mathbf 1_{i+j=n+k}\big)`$.


**Lean.** `NeumannCosineAudit.NeumannCosine.KernelIntegrals.integral_cos_sin_sin` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean#L380): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>

**Lean.** `NeumannCosineAudit.NeumannCosine.KernelIntegrals.integral_cos_cos_cos` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean#L395): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem integral_cos_cos_cos (L : ℝ) (hL : 0 < L) (i j k : ℕ) :
    (∫ x in (0 : ℝ)..L,
      Real.cos ((i : ℝ) * Real.pi * x / L) * Real.cos ((j : ℝ) * Real.pi * x / L) *
        Real.cos ((k : ℝ) * Real.pi * x / L)) =
      L / 4 * ((if (i : ℤ) - j = k then 1 else 0) + (if (i : ℤ) - j = -k then 1 else 0) +
        (if (i : ℤ) + j = k then 1 else 0)) +
        L / 4 * (if k = 0 ∧ i = 0 ∧ j = 0 then 1 else 0)
```

</details>

**Lean.** `NeumannCosineAudit.NeumannCosine.KernelIntegrals.integral_cos_cos_sin_sin` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean#L409): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `d16a23572ff3212856109dda2010668ed7adbf73` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

### Product identities for absolutely summable cosine series

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

For $`L>0`$ and absolutely summable $`u,v,w`$ (given either by $`\sum|u_i|<\infty`$ or as elements of $`\ell^1(\mathbb N)`$), with $`c_m,s_m`$ as above: for $`n,k\ge1`$,


```math
\int_0^L\Big(\sum_iu_ic_i\Big)s_ns_k=\frac L4\big(u_{|n-k|}-u_{n+k}+\mathbf 1_{n=k}u_0\big);
```


for $`k\ge0`$,


```math
\int_0^L\Big(\sum_iu_ic_i\Big)\Big(\sum_jv_jc_j\Big)c_k=\frac L4\Big(\sum_{i-j=k}+\sum_{i-j=-k}+\sum_{i+j=k}\Big)u_iv_j+\frac L4\mathbf 1_{k=0}u_0v_0;
```


and the two-sine and three-series identities of the headline rows hold with summability hypotheses in place of $`\ell^1`$ membership.


**Lean.** `NeumannCosineAudit.NeumannCosine.ProductIdentities.cosine_sine_sine` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean#L429): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>

**Lean.** `NeumannCosineAudit.NeumannCosine.ProductIdentities.two_cosines_two_sines` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean#L441): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>

**Lean.** `NeumannCosineAudit.NeumannCosine.ProductIdentities.cos_cos_cos` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean#L468): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>

**Lean.** `NeumannCosineAudit.NeumannCosine.ProductIdentities.cos_cos_cos_cos` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean#L483): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>

**Lean.** `NeumannCosineAudit.NeumannCosine.ProductIdentities.cosine_sine_sine_lp` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean#L511): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>

**Lean.** `NeumannCosineAudit.NeumannCosine.ProductIdentities.cos_cos_cos_lp` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean#L523): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `d16a23572ff3212856109dda2010668ed7adbf73` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

### Termwise integration of a cosine series

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

Let $`\sum_n|u_n|<\infty`$ and let $`\kappa`$ be continuous with $`|\kappa|\le C`$. Then for all $`a,b,L\in\mathbb R`$,


```math
\sum_n\int_a^bu_n\cos\frac{n\pi x}{L}\,\kappa(x)\,dx=\int_a^b\sum_nu_n\cos\frac{n\pi x}{L}\,\kappa(x)\,dx,
```


the series on the left converging.


**Lean.** `NeumannCosineAudit.NeumannCosine.Series.TermwiseIntegral.hasSum_intervalIntegral_cosine` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean#L545): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `d16a23572ff3212856109dda2010668ed7adbf73` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

### Quadratic decay of the cosine coefficients

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

Under the hypotheses of the $`W^{2,1}`$ rows, with $`w''=(w')'`$ (which exists a.e. and is integrable), for $`k\ge1`$,


```math
w_k=-\Big(\frac{L}{k\pi}\Big)^2\frac2L\int_0^Lw''(x)\cos\frac{k\pi x}{L}\,dx,\qquad|w_k|\le\frac{2L}{\pi^2}\Big(\int_0^L|w''|\Big)\frac1{k^2}.
```


**Lean.** `NeumannCosineAudit.NeumannCosine.Coefficients.cosineCoeff_eq_neg_mul_secondDeriv` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean#L566): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>

**Lean.** `NeumannCosineAudit.NeumannCosine.Coefficients.abs_cosineCoeff_le` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean#L581): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `d16a23572ff3212856109dda2010668ed7adbf73` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

### Summable cosine coefficients of H^2 functions with Neumann trace

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

Under the hypotheses of the $`H^2`$ row, $`\sum_{k\ge0}|w_k|<\infty`$.


**Lean.** `NeumannCosineAudit.NeumannCosine.Sobolev.H2Neumann.H2.summable_norm_cosineCoeff` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean#L602): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

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

</details>


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `d16a23572ff3212856109dda2010668ed7adbf73` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

### Cosine projection of a divergence-form source

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

Let $`L>0`$, $`k\in\mathbb N`$, $`R_0\in L^1(0,L)`$ and $`R_1`$ with $`R_1(0)=R_1(L)=0`$, where either $`R_1`$ is continuous on $`[0,L]`$, differentiable at every point of $`(0,L)`$, with interval-integrable derivative $`R_1'`$, or $`R_1`$ is absolutely continuous on $`[0,L]`$. If $`|R_0|,|R_1|\le B`$ on $`[0,L]`$, then


```math
\Big|\int_0^L\big(R_0(x)+R_1'(x)\big)\cos\frac{k\pi x}{L}\,dx\Big|\le(L+k\pi)B.
```


**Lean.** `NeumannCosineAudit.NeumannCosine.DivergenceFormProjection.abs_integral_source_add_deriv_mul_cos_le` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean#L628): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem abs_integral_source_add_deriv_mul_cos_le {L B : ℝ} (hL : 0 < L) (k : ℕ) {R0 R1 dR1 : ℝ → ℝ}
    (hR0 : IntervalIntegrable R0 volume 0 L)
    (hR1c : ContinuousOn R1 (Icc 0 L)) (hR1d : ∀ x ∈ Ioo 0 L, HasDerivAt R1 (dR1 x) x)
    (hdR1 : IntervalIntegrable dR1 volume 0 L) (h0 : R1 0 = 0) (hL0 : R1 L = 0)
    (hB0 : ∀ x ∈ Icc 0 L, |R0 x| ≤ B) (hB1 : ∀ x ∈ Icc 0 L, |R1 x| ≤ B) :
    |∫ x in (0 : ℝ)..L, (R0 x + dR1 x) * cos (k * π * x / L)| ≤ (L + k * π) * B
```

</details>

**Lean.** `NeumannCosineAudit.NeumannCosine.DivergenceFormProjection.abs_integral_source_add_deriv_mul_cos_le_of_absolutelyContinuous` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean#L640): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem abs_integral_source_add_deriv_mul_cos_le_of_absolutelyContinuous {L B : ℝ} (hL : 0 < L) (k : ℕ)
    {R0 R1 : ℝ → ℝ} (hR0 : IntervalIntegrable R0 volume 0 L)
    (hR1 : AbsolutelyContinuousOnInterval R1 0 L) (h0 : R1 0 = 0) (hL0 : R1 L = 0)
    (hB0 : ∀ x ∈ Icc 0 L, |R0 x| ≤ B) (hB1 : ∀ x ∈ Icc 0 L, |R1 x| ≤ B) :
    |∫ x in (0 : ℝ)..L, (R0 x + deriv R1 x) * cos (k * π * x / L)| ≤ (L + k * π) * B
```

</details>


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `d16a23572ff3212856109dda2010668ed7adbf73` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

### Discrete Neumann eigenvalues: sinc form, ordering and lower bound

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**Statement.**

Let $`\lambda_n^N=\frac{4}{(L/N)^2}\sin^2\frac{n\pi}{2N}`$ and $`N\ge1`$. If $`L\neq0`$ and $`n\ge1`$, then $`\lambda_n^N=(n\pi/L)^2\operatorname{sinc}^2\frac{n\pi}{2N}`$; if $`L\neq0`$ and $`n<k\le N`$, then $`\lambda_n^N<\lambda_k^N`$; if $`L>0`$ and $`1\le n\le N`$, then $`\lambda_1^N\le\lambda_n^N`$; and if $`L>0`$ and $`n\le N`$, then $`\lambda_n^N\ge4n^2/L^2`$.


**Lean.** `NeumannCosineAudit.NeumannCosine.Discrete.Eigenvalues.discreteNeumannEigenvalue_eq_mul_sinc_sq` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean#L655): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem discreteNeumannEigenvalue_eq_mul_sinc_sq (L : ℝ) (n N : ℕ)
    (hL : L ≠ 0) (hn : 0 < n) (hN : 0 < N) :
    4 / (L / (N : ℝ)) ^ 2 * Real.sin ((n : ℝ) * Real.pi / (2 * (N : ℝ))) ^ 2 =
      ((n : ℝ) * Real.pi / L) ^ 2 * Real.sinc ((n : ℝ) * Real.pi / (2 * (N : ℝ))) ^ 2
```

</details>

**Lean.** `NeumannCosineAudit.NeumannCosine.Discrete.Eigenvalues.discreteNeumannEigenvalue_one_le` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean#L665): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem discreteNeumannEigenvalue_one_le (L : ℝ) (n N : ℕ)
    (hL : 0 < L) (hN : 0 < N) (hn : 1 ≤ n) (hnN : n ≤ N) :
    4 / (L / (N : ℝ)) ^ 2 * Real.sin (((1 : ℕ) : ℝ) * Real.pi / (2 * (N : ℝ))) ^ 2 ≤
      4 / (L / (N : ℝ)) ^ 2 * Real.sin ((n : ℝ) * Real.pi / (2 * (N : ℝ))) ^ 2
```

</details>

**Lean.** `NeumannCosineAudit.NeumannCosine.Discrete.Eigenvalues.discreteNeumannEigenvalue_lower_bound` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean#L675): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem discreteNeumannEigenvalue_lower_bound (L : ℝ) (n N : ℕ)
    (hL : 0 < L) (hN : 0 < N) (hnN : n ≤ N) :
    4 * (n : ℝ) ^ 2 / L ^ 2 ≤ 4 / (L / (N : ℝ)) ^ 2 * Real.sin ((n : ℝ) * Real.pi / (2 * (N : ℝ))) ^ 2
```

</details>

**Lean.** `NeumannCosineAudit.NeumannCosine.Discrete.Laplacian.discreteNeumannEigenvalue_lt_of_lt` in [NeumannCosine/Challenge.lean](https://github.com/chenle02/neumann-cosine-lean/blob/d16a23572ff3212856109dda2010668ed7adbf73/NeumannCosine/Challenge.lean#L689): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

<details>
<summary>Exact Lean statement (expand and copy)</summary>

```lean
theorem discreteNeumannEigenvalue_lt_of_lt (L : ℝ) (N n k : ℕ) (hL : L ≠ 0) (hN : 0 < N)
    (hnk : n < k) (hkN : k ≤ N) :
    4 / (L / (N : ℝ)) ^ 2 * Real.sin ((n : ℝ) * Real.pi / (2 * (N : ℝ))) ^ 2 <
      4 / (L / (N : ℝ)) ^ 2 * Real.sin ((k : ℝ) * Real.pi / (2 * (N : ℝ))) ^ 2
```

</details>


Every result with each of its claims, in one table: [Coverage](coverage.md).


**Reference.** L. Chen, I. Ruau and W. Shen, *Chemotaxis models with signal-dependent
sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions* (2026),
[arXiv:2610.20976](https://arxiv.org/abs/2610.20976), provides the motivating application.
Theorem number and page not verified for this standalone result. The exact formal reference is the
Lean statement and source link above; this is not a claim to formalize a numbered paper theorem.

**Compared with the reference.** The statement above retains this library's own hypotheses.
No equivalence to a complete paper theorem, or discharge of application-specific premises, is claimed.

<details>
<summary>Sign-off and trust boundary</summary>

| Check | Recorded status |
|---|---|
| Build and statement comparison | Passed for the linked declarations at the evidence commit |
| Unfinished proofs in the verified proofs | Recorded `sorry_count: 0`; Challenge placeholders are specifications |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Definitions judged independently | No additional definition review claimed by this guide |
| Evidence commit | `d16a23572ff3212856109dda2010668ed7adbf73` |
| Human mathematical review | Not recorded (`formalization.yaml`: unchecked) |
| Prose sign-off | Documentation audit, 2026-10-22; not a new kernel or scientific-review verdict |

</details>

## Not proved here

- No PDE theory: no existence, uniqueness or regularity theorem for any differential equation, and no semigroup.
- No $`L^2`$ theory: completeness of the cosine system in $`L^2(0,L)`$ and Parseval's identity for general $`L^2`$ functions are not proved. The expansions above need summable coefficients, which the library derives from $`W^{2,1}`$ or $`H^2`$ Neumann data.
- No general bridge to Mathlib's `fourierCoeff`. `Coefficients.fourierCoeff_evenPeriodic` covers only the even $`2L`$-periodic extension of a `NeumannW21` function. A bridge for general integrable functions is planned for v0.2.
- One dimension only: no domains in two or more dimensions.

The newer paper companion has its own source and evidence. Its additions are not automatically
part of this standalone library, and neither library establishes whole-paper verification.

<details>
<summary>Lean implementation notes</summary>

The Lean statement, including every binder and hypothesis, controls the result. Definitions may be
total outside their mathematical domain; apply results only under their explicit domain assumptions.
The folded blocks are trusted Challenge statements checked against separate Solution proofs.

</details>

## How this was checked

The [generated verification page](verification.md) and [coverage ledger](coverage.md) retain the
full receipt table and exact declaration mappings. This documentation update changes no Lean source,
claims, toolchain or dependency pins and runs no new proof gate. It does not expand the comparator's
configured scope. See [formalization metadata](https://github.com/chenle02/neumann-cosine-lean/blob/main/formalization.yaml) for recorded review status.

## References and reuse

- [Paper and bibliographic references](https://github.com/chenle02/neumann-cosine-lean/blob/main/README.md#paper-and-references), including the BibTeX entry.
- [Software citation](https://github.com/chenle02/neumann-cosine-lean/blob/main/CITATION.cff) and [license](https://github.com/chenle02/neumann-cosine-lean/blob/main/LICENSE).
- [Paper III source](https://github.com/chenle02/chemotaxis-paper-iii).
- [Paper III Lean companion](https://github.com/chenle02/chemotaxis-paper-iii-lean).
