module
/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/

public import Mathlib

@[expose] public section

/-!
# Headline comparator Challenge: Mathlib-only statements (trusted)

The twelve headline results of `NeumannCosine`, stated in Mathlib vocabulary
only. This module imports Mathlib and nothing else, defines nothing, and every
proof is `sorry` by design. `NeumannCosine.HeadlineSolution` restates each
theorem with the same name and type and proves it from the library.

Every library definition that a library statement uses is written out here in
Mathlib terms; the docstring of each theorem names the definitions unfolded:

* the Neumann mode `mode L k x = cos (k π x / L)`;
* the cosine coefficients `w_0 = (1/L) ∫₀ᴸ w`, `w_k = (2/L) ∫₀ᴸ w(x) cos(k π x / L) dx`;
* test functions `φ ∈ C_c^∞(0,L)`: smooth, compactly supported, `tsupport φ ⊆ (0,L)`;
* the discrete eigenvalue `4 / h² · sin² (n π / (2N))` with mesh width `h = L / N`
  and the continuum eigenvalue `(n π / L)²`.

Name convention: a slot `NeumannCosineHeadline.<D>` is the library declaration `<D>`.
-/

open MeasureTheory Set Filter
open scoped Topology Interval ContDiff

/-! ### 1. Orthogonality and Gram values of the Neumann modes -/

namespace NeumannCosineHeadline.NeumannCosine

/-- **Gram values of the Neumann modes.** For `L > 0` and `m, n ∈ ℕ`,
`∫₀ᴸ cos(mπy/L) cos(nπy/L) dy` is `L` when `m = n = 0`, `L/2` when `m = n ≠ 0`,
and `0` when `m ≠ n`.
Library: `NeumannCosine.integral_mode_mul_mode`, with `mode` unfolded. -/
theorem integral_mode_mul_mode (L : ℝ) (hL : 0 < L) (m n : ℕ) :
    (∫ y in (0 : ℝ)..L,
      Real.cos ((m : ℝ) * Real.pi * y / L) * Real.cos ((n : ℝ) * Real.pi * y / L)) =
      if m = n then (if m = 0 then L else L / 2) else 0 := by
  sorry

end NeumannCosineHeadline.NeumannCosine

/-! ### 2. The four-cosine kernel -/

namespace NeumannCosineHeadline.NeumannCosine.KernelIntegrals

/-- **Four-cosine kernel.** For `L > 0` and `i, j, l, k ∈ ℕ`,
`∫₀ᴸ cos_i cos_j cos_l cos_k = (L/8) (1_{i+j+l=k} + 1_{i+j-l=k} + 1_{i+j-l=-k}
  + 1_{i-j+l=k} + 1_{i-j+l=-k} + 1_{i-j-l=k} + 1_{i-j-l=-k}) + (L/8) 1_{i=j=l=k=0}`,
where `cos_m = cos(mπx/L)` and the index arithmetic is in `ℤ`.
Library: `NeumannCosine.KernelIntegrals.integral_cos_cos_cos_cos`, with `mode`
and `indicatorR P = if P then 1 else 0` unfolded. -/
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
        L / 8 * (if k = 0 ∧ i = 0 ∧ j = 0 ∧ l = 0 then 1 else 0) := by
  sorry

end NeumannCosineHeadline.NeumannCosine.KernelIntegrals

/-! ### 3–4. Integrals of products of absolutely summable cosine series -/

namespace NeumannCosineHeadline.NeumannCosine.ProductIdentities

/-- **Product of three cosine series against a cosine.** For `L > 0`, sequences
`u, v, w ∈ ℓ¹(ℕ)` and `k ∈ ℕ`, the integral over `[0, L]` of
`(∑ uᵢ cos(iπx/L)) (∑ vⱼ cos(jπx/L)) (∑ w_l cos(lπx/L)) cos(kπx/L)` equals `L/8`
times the sum, over the seven sign patterns `i ± j ± l = ±k` listed, of the
constrained convolution sums `∑ uᵢ vⱼ w_l`, plus `(L/8) u₀ v₀ w₀` when `k = 0`.
Library: `NeumannCosine.ProductIdentities.cos_cos_cos_cos_lp` (verbatim). -/
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
        L / 8 * (if k = 0 then u 0 * v 0 * w 0 else 0) := by
  sorry

/-- **Product of two cosine series against two sines.** For `L > 0`,
`u, v ∈ ℓ¹(ℕ)` and `n, k ≥ 1`, the integral over `[0, L]` of
`(∑ uᵢ cos(iπx/L)) (∑ vⱼ cos(jπx/L)) sin(nπx/L) sin(kπx/L)` equals `L/8` times
the signed sum of the seven constrained convolution sums `∑ uᵢ vⱼ` over
`i ∓ j = ±(n - k)` (sign `+`) and `i - j = ±(n + k)`, `i + j = n + k` (sign `-`).
Library: `NeumannCosine.ProductIdentities.two_cosines_two_sines_lp` (verbatim). -/
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
            u p.1.1 * v p.1.2)) := by
  sorry

end NeumannCosineHeadline.NeumannCosine.ProductIdentities

/-! ### 5–6. Cosine coefficients of `W^{2,1}` functions with Neumann data -/

namespace NeumannCosineHeadline.NeumannCosine.Coefficients

/-- **Absolutely summable cosine coefficients.** Let `L > 0` and let `w` be
absolutely continuous on `[0, L]` with derivative `w'` at every interior point,
where `w'` is itself absolutely continuous on `[0, L]` (so `w ∈ W^{2,1}(0,L)`) and
satisfies the Neumann condition `w'(0) = w'(L) = 0`. Then the cosine coefficients
`w_0 = (1/L) ∫₀ᴸ w`, `w_k = (2/L) ∫₀ᴸ w(x) cos(kπx/L) dx` (`k ≥ 1`) satisfy
`∑ₖ |w_k| < ∞`.
Library: `NeumannCosine.Coefficients.summable_norm_cosineCoeff`, with the five
fields of `NeumannW21 L w w'` as separate hypotheses and `cosineCoeff` unfolded. -/
theorem summable_norm_cosineCoeff (L : ℝ) (hL : 0 < L) {w w' : ℝ → ℝ}
    (hac : AbsolutelyContinuousOnInterval w 0 L)
    (hderiv : ∀ x ∈ Ioo 0 L, HasDerivAt w (w' x) x)
    (hac' : AbsolutelyContinuousOnInterval w' 0 L)
    (hleft : w' 0 = 0) (hright : w' L = 0) :
    Summable fun k : ℕ =>
      ‖(if k = 0 then 1 / L else 2 / L) *
        ∫ x in (0 : ℝ)..L, w x * Real.cos ((k : ℝ) * Real.pi * x / L)‖ := by
  sorry

/-- **Pointwise cosine expansion.** Under the hypotheses of
`summable_norm_cosineCoeff`, for every `x ∈ [0, L]` the cosine series
`∑ₖ w_k cos(kπx/L)` converges (absolutely) to `w(x)`.
Library: `NeumannCosine.Coefficients.hasSum_cosineCoeff`, with the five fields of
`NeumannW21 L w w'` as separate hypotheses and `cosineCoeff` unfolded. -/
theorem hasSum_cosineCoeff (L : ℝ) (hL : 0 < L) {w w' : ℝ → ℝ}
    (hac : AbsolutelyContinuousOnInterval w 0 L)
    (hderiv : ∀ x ∈ Ioo 0 L, HasDerivAt w (w' x) x)
    (hac' : AbsolutelyContinuousOnInterval w' 0 L)
    (hleft : w' 0 = 0) (hright : w' L = 0) {x : ℝ} (hx : x ∈ Icc 0 L) :
    HasSum (fun k : ℕ =>
      ((if k = 0 then 1 / L else 2 / L) *
        ∫ y in (0 : ℝ)..L, w y * Real.cos ((k : ℝ) * Real.pi * y / L)) *
        Real.cos ((k : ℝ) * Real.pi * x / L)) (w x) := by
  sorry

end NeumannCosineHeadline.NeumannCosine.Coefficients

/-! ### 7–8. One-dimensional weak derivatives -/

namespace NeumannCosineHeadline.NeumannCosine.Sobolev.WeakDerivative

/-- **du Bois-Reymond lemma.** If `L > 0`, `h ∈ L¹(0,L)` and `∫₀ᴸ h φ' = 0` for
every `φ ∈ C_c^∞(0,L)` (smooth, compactly supported, `tsupport φ ⊆ (0,L)`), then
`h` is almost everywhere equal to a constant on `(0,L)`.
Library: `NeumannCosine.Sobolev.WeakDerivative.ae_eq_const_of_integral_mul_deriv_eq_zero`,
with `IsTestFunction L φ = ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ioo 0 L`
unfolded. -/
theorem ae_eq_const_of_integral_mul_deriv_eq_zero {L : ℝ} (hL : 0 < L) {h : ℝ → ℝ}
    (hh : IntervalIntegrable h volume 0 L)
    (H : ∀ φ : ℝ → ℝ, (ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ioo 0 L) →
      ∫ x in (0 : ℝ)..L, h x * deriv φ x = 0) :
    ∃ c : ℝ, ∀ᵐ x, x ∈ Ioo 0 L → h x = c := by
  sorry

/-- **`W^{1,1}` functions are absolutely continuous.** Let `L > 0` and
`w, g ∈ L¹(0,L)` with `∫₀ᴸ w φ' = -∫₀ᴸ g φ` for every `φ ∈ C_c^∞(0,L)` (`g` is the
weak derivative of `w`). Then for some constant `c` the primitive
`W(x) = c + ∫₀ˣ g` equals `w` a.e. on `(0,L)`, is absolutely continuous on
`[0, L]`, and has derivative `g(x)` at almost every `x ∈ [0, L]`.
Library: `NeumannCosine.Sobolev.WeakDerivative.HasWeakDeriv.ae_eq_primitive`, with the
three fields of `HasWeakDeriv L w g` as separate hypotheses and `IsTestFunction`
unfolded. -/
theorem HasWeakDeriv.ae_eq_primitive {L : ℝ} (hL : 0 < L) {w g : ℝ → ℝ}
    (hw : IntervalIntegrable w volume 0 L) (hg : IntervalIntegrable g volume 0 L)
    (hwg : ∀ φ : ℝ → ℝ, (ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ioo 0 L) →
      ∫ x in (0 : ℝ)..L, w x * deriv φ x = -∫ x in (0 : ℝ)..L, g x * φ x) :
    ∃ c : ℝ, (∀ᵐ x, x ∈ Ioo 0 L → w x = c + ∫ t in (0 : ℝ)..x, g t) ∧
      AbsolutelyContinuousOnInterval (fun x => c + ∫ t in (0 : ℝ)..x, g t) 0 L ∧
      ∀ᵐ x, x ∈ Icc 0 L → HasDerivAt (fun x => c + ∫ t in (0 : ℝ)..x, g t) (g x) x := by
  sorry

end NeumannCosineHeadline.NeumannCosine.Sobolev.WeakDerivative

/-! ### 9. `H²(0,L)` with Neumann trace -/

namespace NeumannCosineHeadline.NeumannCosine.Sobolev.H2Neumann

/-- **Cosine expansion in `H²` with Neumann data.** Let `L > 0` and let
`w, w₁, w₂ ∈ L²(0,L)` with `w₁` the weak derivative of `w` and `w₂` the weak
derivative of `w₁` (tested against every `φ ∈ C_c^∞(0,L)`), so `w ∈ H²(0,L)`.
Assume the Neumann trace condition: some `V` continuous on `[0, L]` agrees with
`w₁` a.e. on `(0,L)` and `V(0) = V(L) = 0`. Then some `W` continuous on `[0, L]`
agrees with `w` a.e. on `(0,L)`, and for every `x ∈ [0, L]`, `W(x) = ∑ₖ w_k cos(kπx/L)`,
with `w_0 = (1/L) ∫₀ᴸ w` and `w_k = (2/L) ∫₀ᴸ w(y) cos(kπy/L) dy` for `k ≥ 1`.
Library: `NeumannCosine.Sobolev.H2Neumann.H2.hasSum_cosineCoeff`, with the five
fields of `H2 L w w₁ w₂` as separate hypotheses and `NeumannTrace`, `IsTestFunction`
and `cosineCoeff` unfolded. -/
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
          Real.cos ((k : ℝ) * Real.pi * x / L)) (W x) := by
  sorry

end NeumannCosineHeadline.NeumannCosine.Sobolev.H2Neumann

/-! ### 10. The discrete Neumann Laplacian -/

namespace NeumannCosineHeadline.NeumannCosine.Discrete.Laplacian

/-- **Cosine eigenpairs of the discrete Neumann Laplacian.** Let `L ≠ 0`,
`N ≥ 1`, `h = L / N`, and `0 ≤ n ≤ N`. On the grid `{0, 1, …, N}` (`Fin (N + 1)`)
let `u j = cos(nπj/N)`. The three-point negative Laplacian
`(2 u_i - u_{i-1} - u_{i+1}) / h²`, with the Neumann condition imposed by
reflected ghost points (at `i = 0` the missing left neighbour is `u_1`, at `i = N`
the missing right neighbour is `u_{N-1}`), maps `u` to `λ u` with
`λ = 4/h² · sin²(nπ/(2N))`. In `Fin (N + 1)`, `i + 1` and `i - 1` are taken
modulo `N + 1`; they are used only where they are the true neighbours.
Library: `NeumannCosine.Discrete.Laplacian.reflectedNegLaplacian_cosine_eigenpair`,
evaluated at each grid point, with `reflectedNegLaplacian`, `reflectedPrev`,
`reflectedNext`, `meshWidth`, `discreteCosineMode` and `discreteNeumannEigenvalue`
unfolded. -/
theorem reflectedNegLaplacian_cosine_eigenpair (L : ℝ) (N n : ℕ) (hL : L ≠ 0)
    (hN : 0 < N) (hnN : n ≤ N) (u : Fin (N + 1) → ℝ)
    (hu : ∀ j : Fin (N + 1), u j = Real.cos ((n : ℝ) * Real.pi * ((j : ℕ) : ℝ) / (N : ℝ)))
    (i : Fin (N + 1)) :
    (2 * u i - u (if (i : ℕ) = 0 then i + 1 else i - 1) -
        u (if (i : ℕ) = N then i - 1 else i + 1)) / (L / (N : ℝ)) ^ 2 =
      4 / (L / (N : ℝ)) ^ 2 * Real.sin ((n : ℝ) * Real.pi / (2 * (N : ℝ))) ^ 2 * u i := by
  sorry

/-- **The discrete cosines exhaust the grid functions.** For `L ≠ 0` and `N ≥ 1`,
every real function `u` on the grid `{0, 1, …, N}` is a linear combination of the
`N + 1` discrete cosines `j ↦ cos(nπj/N)`, `0 ≤ n ≤ N`. Together with the
eigenpairs above (whose eigenvalues are distinct), this says the cosines are a
complete eigenbasis of the discrete Neumann Laplacian.
Library: `NeumannCosine.Discrete.Laplacian.discreteCosineMode_exhaustion`, with
`GridFunction N = Fin (N + 1) → ℝ` and `discreteCosineMode` unfolded. -/
theorem discreteCosineMode_exhaustion (L : ℝ) (N : ℕ) (hL : L ≠ 0) (hN : 0 < N)
    (u : Fin (N + 1) → ℝ) :
    ∃ c : Fin (N + 1) → ℝ,
      ∑ n : Fin (N + 1), c n • (fun j : Fin (N + 1) =>
        Real.cos (((n : ℕ) : ℝ) * Real.pi * ((j : ℕ) : ℝ) / (N : ℝ))) = u := by
  sorry

end NeumannCosineHeadline.NeumannCosine.Discrete.Laplacian

/-! ### 11. Convergence of the discrete eigenvalues -/

namespace NeumannCosineHeadline.NeumannCosine.Discrete.Eigenvalues

/-- **Discrete eigenvalues converge.** For `L > 0` and a fixed mode `n ≥ 1`, the
discrete Neumann eigenvalue `4/h² · sin²(nπ/(2N))` with `h = L/N` tends to the
continuum eigenvalue `(nπ/L)²` as `N → ∞`.
Library: `NeumannCosine.Discrete.Eigenvalues.discreteNeumannEigenvalue_tendsto`, with
`discreteNeumannEigenvalue`, `discreteHalfAngle` and `neumannEigenvalue` unfolded. -/
theorem discreteNeumannEigenvalue_tendsto (L : ℝ) (n : ℕ) (hL : 0 < L) (hn : 0 < n) :
    Tendsto (fun N : ℕ =>
        4 / (L / (N : ℝ)) ^ 2 * Real.sin ((n : ℝ) * Real.pi / (2 * (N : ℝ))) ^ 2)
      atTop (𝓝 (((n : ℝ) * Real.pi / L) ^ 2)) := by
  sorry

end NeumannCosineHeadline.NeumannCosine.Discrete.Eigenvalues

/-! ### 12. Discrete-to-continuum modal minimum -/

namespace NeumannCosineHeadline.NeumannCosine.Discrete.ModalMinimumLimit

/-- **Modal-minimum convergence.** Let `L > 0`, `K > 0`, and let `f : ℝ → ℝ` be
continuous at every `x > 0` with `K x ≤ f x` for `x > 0`. Then the minimum of
`f(λ_n^N)` over the discrete modes `1 ≤ n ≤ N`, where
`λ_n^N = 4/(L/N)² · sin²(nπ/(2N))`, tends as `N → ∞` to the infimum of `f((nπ/L)²)`
over all modes `n ≥ 1`. (For `N = 0` the set is empty and `sInf ∅ = 0` in `ℝ`.)
Library: `NeumannCosine.Discrete.ModalMinimumLimit.discreteModalMin_tendsto`, with
`continuumModalInf` and the eigenvalues unfolded and the finite minimum
`discreteModalMin f L N` (a `Finset.inf'` over `positiveModes N = Finset.Icc 1 N`,
and `0` for `N = 0`) written as the infimum of the same finite set. -/
theorem discreteModalMin_tendsto (f : ℝ → ℝ) (K L : ℝ) (hK : 0 < K) (hL : 0 < L)
    (hf : ∀ x : ℝ, 0 < x → ContinuousAt f x)
    (hlow : ∀ x : ℝ, 0 < x → K * x ≤ f x) :
    Tendsto (fun N : ℕ => sInf {y : ℝ | ∃ n : ℕ, 1 ≤ n ∧ n ≤ N ∧
        y = f (4 / (L / (N : ℝ)) ^ 2 * Real.sin ((n : ℝ) * Real.pi / (2 * (N : ℝ))) ^ 2)})
      atTop (𝓝 (sInf {y : ℝ | ∃ n : ℕ, 1 ≤ n ∧ y = f (((n : ℝ) * Real.pi / L) ^ 2)})) := by
  sorry

end NeumannCosineHeadline.NeumannCosine.Discrete.ModalMinimumLimit
