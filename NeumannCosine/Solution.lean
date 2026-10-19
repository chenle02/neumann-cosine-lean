module
/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/

public import Mathlib
public import NeumannCosine.Basic
public import NeumannCosine.KernelIntegrals
public import NeumannCosine.ProductIdentities
public import NeumannCosine.Coefficients
public import NeumannCosine.Sobolev.WeakDerivative
public import NeumannCosine.Sobolev.H2Neumann
public import NeumannCosine.Discrete.Laplacian
public import NeumannCosine.Discrete.Eigenvalues
public import NeumannCosine.Discrete.ModalMinimumLimit

public import NeumannCosine.Series.TermwiseIntegral
public import NeumannCosine.DivergenceFormProjection

@[expose] public section

/-!
# Comparator Solution (untrusted)

Restates every theorem of `NeumannCosine.Challenge` with the same name and the same
statement text, and proves it from the library declaration named in its docstring: by
`exact` (or `apply` and `assumption`) where the Challenge only unfolds definitions, and by a
short bridge where it splits a structure into hypotheses, evaluates a linear map at a point,
or writes a finite minimum as an infimum. Docstrings are copied from the Challenge.
-/

/-! ## Part I: the headline results -/

open MeasureTheory Set Filter
open scoped Topology Interval ContDiff

/-! ### 1. Orthogonality and Gram values of the Neumann modes -/

namespace NeumannCosineAudit.NeumannCosine

/-- **Gram values of the Neumann modes.** For `L > 0` and `m, n ∈ ℕ`,
`∫₀ᴸ cos(mπy/L) cos(nπy/L) dy` is `L` when `m = n = 0`, `L/2` when `m = n ≠ 0`,
and `0` when `m ≠ n`.
Library: `NeumannCosine.integral_mode_mul_mode`, with `mode` unfolded. -/
theorem integral_mode_mul_mode (L : ℝ) (hL : 0 < L) (m n : ℕ) :
    (∫ y in (0 : ℝ)..L,
      Real.cos ((m : ℝ) * Real.pi * y / L) * Real.cos ((n : ℝ) * Real.pi * y / L)) =
      if m = n then (if m = 0 then L else L / 2) else 0 := by
  exact _root_.NeumannCosine.integral_mode_mul_mode L hL m n

end NeumannCosineAudit.NeumannCosine

/-! ### 2. The four-cosine kernel -/

namespace NeumannCosineAudit.NeumannCosine.KernelIntegrals

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
  exact _root_.NeumannCosine.KernelIntegrals.integral_cos_cos_cos_cos L hL i j l k

end NeumannCosineAudit.NeumannCosine.KernelIntegrals

/-! ### 3–4. Integrals of products of absolutely summable cosine series -/

namespace NeumannCosineAudit.NeumannCosine.ProductIdentities

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
  exact _root_.NeumannCosine.ProductIdentities.cos_cos_cos_cos_lp L hL u v w k

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
  exact _root_.NeumannCosine.ProductIdentities.two_cosines_two_sines_lp L hL u v n k hn hk

end NeumannCosineAudit.NeumannCosine.ProductIdentities

/-! ### 5–6. Cosine coefficients of `W^{2,1}` functions with Neumann data -/

namespace NeumannCosineAudit.NeumannCosine.Coefficients

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
  exact _root_.NeumannCosine.Coefficients.summable_norm_cosineCoeff L hL
    ⟨hac, hderiv, hac', hleft, hright⟩

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
  exact _root_.NeumannCosine.Coefficients.hasSum_cosineCoeff L hL
    ⟨hac, hderiv, hac', hleft, hright⟩ hx

end NeumannCosineAudit.NeumannCosine.Coefficients

/-! ### 7–8. One-dimensional weak derivatives -/

namespace NeumannCosineAudit.NeumannCosine.Sobolev.WeakDerivative

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
  exact _root_.NeumannCosine.Sobolev.WeakDerivative.ae_eq_const_of_integral_mul_deriv_eq_zero
    hL hh H

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
  exact _root_.NeumannCosine.Sobolev.WeakDerivative.HasWeakDeriv.ae_eq_primitive hL
    ⟨hw, hg, hwg⟩

end NeumannCosineAudit.NeumannCosine.Sobolev.WeakDerivative

/-! ### 9. `H²(0,L)` with Neumann trace -/

namespace NeumannCosineAudit.NeumannCosine.Sobolev.H2Neumann

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
  exact _root_.NeumannCosine.Sobolev.H2Neumann.H2.hasSum_cosineCoeff hL
    ⟨hw, hw₁, hw₂, hd₁, hd₂⟩ hN

end NeumannCosineAudit.NeumannCosine.Sobolev.H2Neumann

/-! ### 10. The discrete Neumann Laplacian -/

namespace NeumannCosineAudit.NeumannCosine.Discrete.Laplacian

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
  open _root_.NeumannCosine.Discrete.Laplacian
    _root_.NeumannCosine.Discrete.Eigenvalues in
  have hu' : u = discreteCosineMode N n := funext hu
  subst hu'
  have hprev : reflectedPrev N hN i = if (i : ℕ) = 0 then i + 1 else i - 1 := by
    unfold reflectedPrev
    split_ifs with h
    · ext
      rw [Fin.val_add_one_of_lt (by rw [Fin.lt_def, Fin.val_last]; omega)]
      simp [h]
    · ext
      rw [Fin.coe_sub_one, ite_eq_right (fun h' => h (by simpa using congrArg Fin.val h'))]
  have hnext : reflectedNext N hN i = if (i : ℕ) = N then i - 1 else i + 1 := by
    unfold reflectedNext
    split_ifs with h
    · ext
      have h0 : i ≠ 0 := fun h' => by
        rw [h'] at h; simp at h; omega
      rw [Fin.coe_sub_one, ite_eq_right h0, h]
    · ext
      rw [Fin.val_add_one_of_lt (by
        rw [Fin.lt_def, Fin.val_last]; have := i.isLt; omega)]
  have h := congrFun (_root_.NeumannCosine.Discrete.Laplacian.reflectedNegLaplacian_cosine_eigenpair L N n hL hN hnN) i
  rw [← hprev, ← hnext]
  exact h

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
  exact _root_.NeumannCosine.Discrete.Laplacian.discreteCosineMode_exhaustion L N hL hN u

end NeumannCosineAudit.NeumannCosine.Discrete.Laplacian

/-! ### 11. Convergence of the discrete eigenvalues -/

namespace NeumannCosineAudit.NeumannCosine.Discrete.Eigenvalues

/-- **Discrete eigenvalues converge.** For `L > 0` and a fixed mode `n ≥ 1`, the
discrete Neumann eigenvalue `4/h² · sin²(nπ/(2N))` with `h = L/N` tends to the
continuum eigenvalue `(nπ/L)²` as `N → ∞`.
Library: `NeumannCosine.Discrete.Eigenvalues.discreteNeumannEigenvalue_tendsto`, with
`discreteNeumannEigenvalue`, `discreteHalfAngle` and `neumannEigenvalue` unfolded. -/
theorem discreteNeumannEigenvalue_tendsto (L : ℝ) (n : ℕ) (hL : 0 < L) (hn : 0 < n) :
    Tendsto (fun N : ℕ =>
        4 / (L / (N : ℝ)) ^ 2 * Real.sin ((n : ℝ) * Real.pi / (2 * (N : ℝ))) ^ 2)
      atTop (𝓝 (((n : ℝ) * Real.pi / L) ^ 2)) := by
  exact _root_.NeumannCosine.Discrete.Eigenvalues.discreteNeumannEigenvalue_tendsto L n hL hn

end NeumannCosineAudit.NeumannCosine.Discrete.Eigenvalues

/-! ### 12. Discrete-to-continuum modal minimum -/

namespace NeumannCosineAudit.NeumannCosine.Discrete.ModalMinimumLimit

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
  open _root_.NeumannCosine.Discrete.ModalMinimumLimit
    _root_.NeumannCosine.Discrete.Eigenvalues in
  have hfun : (fun N : ℕ => sInf {y : ℝ | ∃ n : ℕ, 1 ≤ n ∧ n ≤ N ∧
      y = f (4 / (L / (N : ℝ)) ^ 2 * Real.sin ((n : ℝ) * Real.pi / (2 * (N : ℝ))) ^ 2)}) =
      discreteModalMin f L := by
    funext N
    unfold discreteModalMin
    split_ifs with hN
    · rw [Finset.inf'_eq_csInf_image]
      congr 1
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.mem_coe, positiveModes,
        Finset.mem_Icc, discreteNeumannEigenvalue, discreteHalfAngle]
      constructor
      · rintro ⟨n, h1, h2, rfl⟩
        exact ⟨n, ⟨h1, h2⟩, rfl⟩
      · rintro ⟨n, ⟨h1, h2⟩, rfl⟩
        exact ⟨n, h1, h2, rfl⟩
    · have hN0 : N = 0 := by omega
      subst hN0
      have hempty : {y : ℝ | ∃ n : ℕ, 1 ≤ n ∧ n ≤ 0 ∧
          y = f (4 / (L / ((0 : ℕ) : ℝ)) ^ 2 *
            Real.sin ((n : ℝ) * Real.pi / (2 * ((0 : ℕ) : ℝ))) ^ 2)} = ∅ := by
        ext y
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨n, h1, h2, -⟩
        omega
      rw [hempty, Real.sInf_empty]
  rw [hfun]
  exact _root_.NeumannCosine.Discrete.ModalMinimumLimit.discreteModalMin_tendsto f K L hK hL hf hlow

end NeumannCosineAudit.NeumannCosine.Discrete.ModalMinimumLimit

/-! ## Part II: further results -/

open MeasureTheory Set Filter
open scoped Topology Interval ContDiff

namespace NeumannCosineAudit.NeumannCosine

/-- `∫₀ᴸ cos (j π y / L) dy` is `L` if `j = 0` and `0` otherwise, for `j ∈ ℤ`.
Library: `NeumannCosine.integral_cos_int_mul_pi_div` (verbatim). -/
theorem integral_cos_int_mul_pi_div (L : ℝ) (hL : 0 < L) (j : ℤ) :
    (∫ y in (0 : ℝ)..L,
      Real.cos (((j : ℝ) * Real.pi / L) * y)) =
        if j = 0 then L else 0 := by
  apply _root_.NeumannCosine.integral_cos_int_mul_pi_div <;> assumption

/-- **Normalized self-projection.** For `L > 0` and `n ≥ 1`,
`(2/L) ∫₀ᴸ cos(nπy/L)² dy = 1`.
Library: `NeumannCosine.normalized_integral_mode_mul_self`, with `mode` unfolded. -/
theorem normalized_integral_mode_mul_self (L : ℝ) (n : ℕ) (hL : 0 < L) (hn : 0 < n) :
    2 / L * (∫ y in (0 : ℝ)..L,
      Real.cos ((n : ℝ) * Real.pi * y / L) * Real.cos ((n : ℝ) * Real.pi * y / L)) = 1 := by
  exact _root_.NeumannCosine.normalized_integral_mode_mul_self L n hL hn

/-- **Third harmonic is orthogonal.** For `L > 0` and `n ≥ 1`,
`(2/L) ∫₀ᴸ cos(3nπy/L) cos(nπy/L) dy = 0`.
Library: `NeumannCosine.normalized_integral_mode_three_mul`, with `mode` unfolded. -/
theorem normalized_integral_mode_three_mul (L : ℝ) (n : ℕ) (hL : 0 < L) (hn : 0 < n) :
    2 / L * (∫ y in (0 : ℝ)..L,
      Real.cos (((3 * n : ℕ) : ℝ) * Real.pi * y / L) * Real.cos ((n : ℝ) * Real.pi * y / L)) = 0 := by
  exact _root_.NeumannCosine.normalized_integral_mode_three_mul L n hL hn

/-- **Fourth moment of a mode.** For `L > 0` and `n ≥ 1`,
`(2/L) ∫₀ᴸ cos(nπy/L)³ cos(nπy/L) dy = 3/4`.
Library: `NeumannCosine.normalized_integral_mode_pow_four`, with `mode` unfolded. -/
theorem normalized_integral_mode_pow_four (L : ℝ) (n : ℕ) (hL : 0 < L) (hn : 0 < n) :
    2 / L * (∫ y in (0 : ℝ)..L,
      Real.cos ((n : ℝ) * Real.pi * y / L) ^ 3 * Real.cos ((n : ℝ) * Real.pi * y / L)) = 3 / 4 := by
  exact _root_.NeumannCosine.normalized_integral_mode_pow_four L n hL hn

end NeumannCosineAudit.NeumannCosine

namespace NeumannCosineAudit.NeumannCosine.KernelIntegrals

/-- **One-cosine/two-sine kernel.** For `L > 0`, `i ∈ ℕ` and `n, k ≥ 1`,
`∫₀ᴸ cos(iπx/L) sin(nπx/L) sin(kπx/L) dx = (L/4)(1_{i=|n-k|} - 1_{i=n+k} + 1_{n=k, i=0})`.
Library: `NeumannCosine.KernelIntegrals.integral_cos_sin_sin`, with `mode`, `sinMode` and
`indicatorR P = if P then 1 else 0` unfolded. -/
theorem integral_cos_sin_sin (L : ℝ) (hL : 0 < L) (i n k : ℕ)
    (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (∫ x in (0 : ℝ)..L,
      Real.cos ((i : ℝ) * Real.pi * x / L) * Real.sin ((n : ℝ) * Real.pi * x / L) *
        Real.sin ((k : ℝ) * Real.pi * x / L)) =
      L / 4 * ((if i = Int.natAbs ((n : ℤ) - k) then 1 else 0) -
        (if i = n + k then 1 else 0) +
        (if n = k ∧ i = 0 then 1 else 0)) := by
  exact _root_.NeumannCosine.KernelIntegrals.integral_cos_sin_sin L hL i n k hn hk

/-- **Three-cosine kernel.** For `L > 0` and `i, j, k ∈ ℕ`,
`∫₀ᴸ cos_i cos_j cos_k = (L/4)(1_{i-j=k} + 1_{i-j=-k} + 1_{i+j=k}) + (L/4) 1_{i=j=k=0}`,
where `cos_m = cos(mπx/L)` and the index arithmetic is in `ℤ`.
Library: `NeumannCosine.KernelIntegrals.integral_cos_cos_cos`, with `mode` and
`indicatorR` unfolded. -/
theorem integral_cos_cos_cos (L : ℝ) (hL : 0 < L) (i j k : ℕ) :
    (∫ x in (0 : ℝ)..L,
      Real.cos ((i : ℝ) * Real.pi * x / L) * Real.cos ((j : ℝ) * Real.pi * x / L) *
        Real.cos ((k : ℝ) * Real.pi * x / L)) =
      L / 4 * ((if (i : ℤ) - j = k then 1 else 0) + (if (i : ℤ) - j = -k then 1 else 0) +
        (if (i : ℤ) + j = k then 1 else 0)) +
        L / 4 * (if k = 0 ∧ i = 0 ∧ j = 0 then 1 else 0) := by
  exact _root_.NeumannCosine.KernelIntegrals.integral_cos_cos_cos L hL i j k

/-- **Two-cosine/two-sine kernel.** For `L > 0`, `i, j ∈ ℕ` and `n, k ≥ 1`,
`∫₀ᴸ cos_i cos_j sin_n sin_k` is `L/8` times the seven signed indicators displayed
(index arithmetic in `ℤ`).
Library: `NeumannCosine.KernelIntegrals.integral_cos_cos_sin_sin`, with `mode`, `sinMode`
and `indicatorR` unfolded. -/
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
        (if (i : ℤ) + j = (n : ℤ) + k then 1 else 0)) := by
  exact _root_.NeumannCosine.KernelIntegrals.integral_cos_cos_sin_sin L hL i j n k hn hk

end NeumannCosineAudit.NeumannCosine.KernelIntegrals

namespace NeumannCosineAudit.NeumannCosine.ProductIdentities

/-- One cosine series against two sine modes (`n, k ≥ 1`).
Library: `NeumannCosine.ProductIdentities.cosine_sine_sine` (verbatim). -/
theorem cosine_sine_sine (L : ℝ) (hL : 0 < L) (u : ℕ → ℝ)
    (hu : Summable fun i => ‖u i‖) (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∫ x in (0 : ℝ)..L,
        (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
          Real.sin ((n : ℝ) * Real.pi * x / L) *
          Real.sin ((k : ℝ) * Real.pi * x / L) =
      L / 4 * (u (Int.natAbs ((n : ℤ) - k)) - u (n + k) +
        (if n = k then u 0 else 0)) := by
  apply _root_.NeumannCosine.ProductIdentities.cosine_sine_sine <;> assumption

/-- Two cosine series against two sine modes (`n, k ≥ 1`).
Library: `NeumannCosine.ProductIdentities.two_cosines_two_sines` (verbatim). -/
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
            u p.1.1 * v p.1.2)) := by
  apply _root_.NeumannCosine.ProductIdentities.two_cosines_two_sines <;> assumption

/-- Two cosine series against one cosine mode (`k ≥ 0`).
Library: `NeumannCosine.ProductIdentities.cos_cos_cos` (verbatim). -/
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
        L / 4 * (if k = 0 then u 0 * v 0 else 0) := by
  apply _root_.NeumannCosine.ProductIdentities.cos_cos_cos <;> assumption

/-- Three cosine series against one cosine mode (`k ≥ 0`).
Library: `NeumannCosine.ProductIdentities.cos_cos_cos_cos` (verbatim). -/
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
        L / 8 * (if k = 0 then u 0 * v 0 * w 0 else 0) := by
  apply _root_.NeumannCosine.ProductIdentities.cos_cos_cos_cos <;> assumption

/-- `cosine_sine_sine` for `u ∈ ℓ¹(ℕ₀)`.
Library: `NeumannCosine.ProductIdentities.cosine_sine_sine_lp` (verbatim). -/
theorem cosine_sine_sine_lp (L : ℝ) (hL : 0 < L)
    (u : lp (fun _ : ℕ => ℝ) 1) (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∫ x in (0 : ℝ)..L,
        (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
          Real.sin ((n : ℝ) * Real.pi * x / L) *
          Real.sin ((k : ℝ) * Real.pi * x / L) =
      L / 4 * (u (Int.natAbs ((n : ℤ) - k)) - u (n + k) +
        (if n = k then u 0 else 0)) := by
  apply _root_.NeumannCosine.ProductIdentities.cosine_sine_sine_lp <;> assumption

/-- `cos_cos_cos` for `u, v ∈ ℓ¹(ℕ₀)`.
Library: `NeumannCosine.ProductIdentities.cos_cos_cos_lp` (verbatim). -/
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
        L / 4 * (if k = 0 then u 0 * v 0 else 0) := by
  apply _root_.NeumannCosine.ProductIdentities.cos_cos_cos_lp <;> assumption

end NeumannCosineAudit.NeumannCosine.ProductIdentities

namespace NeumannCosineAudit.NeumannCosine.Series.TermwiseIntegral

/-- **Termwise integration of a cosine series.** For `u ∈ ℓ¹(ℕ)` and a continuous
kernel bounded by `C`, the integrals over `[a, b]` of `uₙ cos(nπx/L) kernel(x)` sum to the
integral of `∑ₙ uₙ cos(nπx/L) kernel(x)`.
Library: `NeumannCosine.Series.TermwiseIntegral.hasSum_intervalIntegral_cosine`, with
`mode` unfolded. -/
theorem hasSum_intervalIntegral_cosine (a b L : ℝ) (u : ℕ → ℝ)
    (kernel : ℝ → ℝ) (C : ℝ)
    (hu : Summable fun n => ‖u n‖)
    (hkernel_cont : Continuous kernel)
    (hkernel : ∀ x, ‖kernel x‖ ≤ C) (hC : 0 ≤ C) :
    HasSum
      (fun n : ℕ => ∫ x in a..b,
        u n * Real.cos ((n : ℝ) * Real.pi * x / L) * kernel x)
      (∫ x in a..b, ∑' n : ℕ,
        u n * Real.cos ((n : ℝ) * Real.pi * x / L) * kernel x) := by
  exact _root_.NeumannCosine.Series.TermwiseIntegral.hasSum_intervalIntegral_cosine a b L u
    kernel C hu hkernel_cont hkernel hC

end NeumannCosineAudit.NeumannCosine.Series.TermwiseIntegral

namespace NeumannCosineAudit.NeumannCosine.Coefficients

/-- **Coefficients by two integrations by parts.** For `w` as in
`summable_norm_cosineCoeff` (absolutely continuous on `[0, L]`, derivative `w'` on `(0, L)`,
`w'` absolutely continuous, `w'(0) = w'(L) = 0`) and `k ≥ 1`,
`w_k = -(L/(kπ))² · (2/L) ∫₀ᴸ w''(x) cos(kπx/L) dx` with `w'' = deriv w'`.
Library: `NeumannCosine.Coefficients.cosineCoeff_eq_neg_mul_secondDeriv`, with the five fields of `NeumannW21 L w w'` as separate hypotheses and `cosineCoeff` unfolded. -/
theorem cosineCoeff_eq_neg_mul_secondDeriv (L : ℝ) (hL : 0 < L) {w w' : ℝ → ℝ}
    (hac : AbsolutelyContinuousOnInterval w 0 L)
    (hderiv : ∀ x ∈ Ioo 0 L, HasDerivAt w (w' x) x)
    (hac' : AbsolutelyContinuousOnInterval w' 0 L)
    (hleft : w' 0 = 0) (hright : w' L = 0) {k : ℕ} (hk : k ≠ 0) :
    (if k = 0 then 1 / L else 2 / L) *
        ∫ x in (0 : ℝ)..L, w x * Real.cos ((k : ℝ) * Real.pi * x / L) =
      -(L / ((k : ℝ) * Real.pi)) ^ 2 *
        (2 / L * ∫ x in (0 : ℝ)..L,
          deriv w' x * Real.cos ((k : ℝ) * Real.pi * x / L)) := by
  exact _root_.NeumannCosine.Coefficients.cosineCoeff_eq_neg_mul_secondDeriv L hL
    ⟨hac, hderiv, hac', hleft, hright⟩ hk

/-- **Quadratic decay of the coefficients.** For `w` as in `summable_norm_cosineCoeff`
and `k ≥ 1`, `|w_k| ≤ (2L/π²) (∫₀ᴸ |w''|) / k²` with `w'' = deriv w'`.
Library: `NeumannCosine.Coefficients.abs_cosineCoeff_le`, with the five fields of `NeumannW21 L w w'` as separate hypotheses and `cosineCoeff` unfolded. -/
theorem abs_cosineCoeff_le (L : ℝ) (hL : 0 < L) {w w' : ℝ → ℝ}
    (hac : AbsolutelyContinuousOnInterval w 0 L)
    (hderiv : ∀ x ∈ Ioo 0 L, HasDerivAt w (w' x) x)
    (hac' : AbsolutelyContinuousOnInterval w' 0 L)
    (hleft : w' 0 = 0) (hright : w' L = 0) {k : ℕ} (hk : k ≠ 0) :
    |(if k = 0 then 1 / L else 2 / L) *
        ∫ x in (0 : ℝ)..L, w x * Real.cos ((k : ℝ) * Real.pi * x / L)| ≤
      2 * L / Real.pi ^ 2 * (∫ x in (0 : ℝ)..L, |deriv w' x|) *
        (1 / (k : ℝ) ^ 2) := by
  exact _root_.NeumannCosine.Coefficients.abs_cosineCoeff_le L hL
    ⟨hac, hderiv, hac', hleft, hright⟩ hk

end NeumannCosineAudit.NeumannCosine.Coefficients

namespace NeumannCosineAudit.NeumannCosine.Sobolev.H2Neumann

/-- **Summable coefficients in `H²` with Neumann data.** Under the hypotheses of
`H2.hasSum_cosineCoeff` (`w ∈ H²(0,L)` with weak derivatives `w₁, w₂` and the Neumann
trace `w₁(0) = w₁(L) = 0` of the continuous representative), `∑ₖ |w_k| < ∞`.
Library: `NeumannCosine.Sobolev.H2Neumann.H2.summable_norm_cosineCoeff`, with the five
fields of `H2 L w w₁ w₂` as separate hypotheses and `NeumannTrace`, `IsTestFunction`
and `cosineCoeff` unfolded. -/
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
        ∫ x in (0 : ℝ)..L, w x * Real.cos ((k : ℝ) * Real.pi * x / L)‖ := by
  exact _root_.NeumannCosine.Sobolev.H2Neumann.H2.summable_norm_cosineCoeff hL
    ⟨hw, hw₁, hw₂, hd₁, hd₂⟩ hN

end NeumannCosineAudit.NeumannCosine.Sobolev.H2Neumann

namespace NeumannCosineAudit.NeumannCosine.DivergenceFormProjection

open Real

/-- **Projection bound** (differentiable `R₁`). For `L > 0` and `k : ℕ`, let `R₁` be
continuous on `[0, L]` with derivative `dR₁` on `(0, L)`, `dR₁` interval integrable,
`R₁ 0 = R₁ L = 0`, and let `R₀` be interval integrable, with `|R₀|, |R₁| ≤ B` on `[0, L]`. Then
`|∫₀ᴸ (R₀ + dR₁) cos(kπx/L) dx| ≤ (L + kπ) B`.
Library: `NeumannCosine.DivergenceFormProjection.abs_integral_source_add_deriv_mul_cos_le` (verbatim). -/
theorem abs_integral_source_add_deriv_mul_cos_le {L B : ℝ} (hL : 0 < L) (k : ℕ) {R0 R1 dR1 : ℝ → ℝ}
    (hR0 : IntervalIntegrable R0 volume 0 L)
    (hR1c : ContinuousOn R1 (Icc 0 L)) (hR1d : ∀ x ∈ Ioo 0 L, HasDerivAt R1 (dR1 x) x)
    (hdR1 : IntervalIntegrable dR1 volume 0 L) (h0 : R1 0 = 0) (hL0 : R1 L = 0)
    (hB0 : ∀ x ∈ Icc 0 L, |R0 x| ≤ B) (hB1 : ∀ x ∈ Icc 0 L, |R1 x| ≤ B) :
    |∫ x in (0 : ℝ)..L, (R0 x + dR1 x) * cos (k * π * x / L)| ≤ (L + k * π) * B := by
  apply _root_.NeumannCosine.DivergenceFormProjection.abs_integral_source_add_deriv_mul_cos_le <;> assumption

/-- **Projection bound** (absolutely continuous `R₁`). As `abs_integral_source_add_deriv_mul_cos_le`,
with `R₁` absolutely continuous on `[0, L]` and its derivative `deriv R₁`, which exists
almost everywhere and is integrable (Mathlib's `AbsolutelyContinuousOnInterval`).
Library: `NeumannCosine.DivergenceFormProjection.abs_integral_source_add_deriv_mul_cos_le_of_absolutelyContinuous` (verbatim). -/
theorem abs_integral_source_add_deriv_mul_cos_le_of_absolutelyContinuous {L B : ℝ} (hL : 0 < L) (k : ℕ)
    {R0 R1 : ℝ → ℝ} (hR0 : IntervalIntegrable R0 volume 0 L)
    (hR1 : AbsolutelyContinuousOnInterval R1 0 L) (h0 : R1 0 = 0) (hL0 : R1 L = 0)
    (hB0 : ∀ x ∈ Icc 0 L, |R0 x| ≤ B) (hB1 : ∀ x ∈ Icc 0 L, |R1 x| ≤ B) :
    |∫ x in (0 : ℝ)..L, (R0 x + deriv R1 x) * cos (k * π * x / L)| ≤ (L + k * π) * B := by
  apply _root_.NeumannCosine.DivergenceFormProjection.abs_integral_source_add_deriv_mul_cos_le_of_absolutelyContinuous <;> assumption

end NeumannCosineAudit.NeumannCosine.DivergenceFormProjection

namespace NeumannCosineAudit.NeumannCosine.Discrete.Eigenvalues

/-- **Discrete eigenvalue as a `sinc²` correction.** For `L ≠ 0`, `n ≥ 1`, `N ≥ 1`,
`4/(L/N)² · sin²(nπ/(2N)) = (nπ/L)² · sinc²(nπ/(2N))`.
Library: `NeumannCosine.Discrete.Eigenvalues.discreteNeumannEigenvalue_eq_mul_sinc_sq`, with
`discreteNeumannEigenvalue`, `neumannEigenvalue` and `discreteHalfAngle` unfolded. -/
theorem discreteNeumannEigenvalue_eq_mul_sinc_sq (L : ℝ) (n N : ℕ)
    (hL : L ≠ 0) (hn : 0 < n) (hN : 0 < N) :
    4 / (L / (N : ℝ)) ^ 2 * Real.sin ((n : ℝ) * Real.pi / (2 * (N : ℝ))) ^ 2 =
      ((n : ℝ) * Real.pi / L) ^ 2 * Real.sinc ((n : ℝ) * Real.pi / (2 * (N : ℝ))) ^ 2 := by
  exact _root_.NeumannCosine.Discrete.Eigenvalues.discreteNeumannEigenvalue_eq_mul_sinc_sq
    L n N hL hn hN

/-- **The first mode has the smallest discrete eigenvalue.** For `L > 0`, `N ≥ 1` and
`1 ≤ n ≤ N`, `λ_1^N ≤ λ_n^N` where `λ_n^N = 4/(L/N)² · sin²(nπ/(2N))`.
Library: `NeumannCosine.Discrete.Eigenvalues.discreteNeumannEigenvalue_one_le`, with
`discreteNeumannEigenvalue` and `discreteHalfAngle` unfolded. -/
theorem discreteNeumannEigenvalue_one_le (L : ℝ) (n N : ℕ)
    (hL : 0 < L) (hN : 0 < N) (hn : 1 ≤ n) (hnN : n ≤ N) :
    4 / (L / (N : ℝ)) ^ 2 * Real.sin (((1 : ℕ) : ℝ) * Real.pi / (2 * (N : ℝ))) ^ 2 ≤
      4 / (L / (N : ℝ)) ^ 2 * Real.sin ((n : ℝ) * Real.pi / (2 * (N : ℝ))) ^ 2 := by
  exact _root_.NeumannCosine.Discrete.Eigenvalues.discreteNeumannEigenvalue_one_le
    L n N hL hN hn hnN

/-- **Uniform lower bound.** For `L > 0`, `N ≥ 1` and `n ≤ N`,
`4n²/L² ≤ 4/(L/N)² · sin²(nπ/(2N))`.
Library: `NeumannCosine.Discrete.Eigenvalues.discreteNeumannEigenvalue_lower_bound`, with
`discreteNeumannEigenvalue` and `discreteHalfAngle` unfolded. -/
theorem discreteNeumannEigenvalue_lower_bound (L : ℝ) (n N : ℕ)
    (hL : 0 < L) (hN : 0 < N) (hnN : n ≤ N) :
    4 * (n : ℝ) ^ 2 / L ^ 2 ≤ 4 / (L / (N : ℝ)) ^ 2 * Real.sin ((n : ℝ) * Real.pi / (2 * (N : ℝ))) ^ 2 := by
  exact _root_.NeumannCosine.Discrete.Eigenvalues.discreteNeumannEigenvalue_lower_bound
    L n N hL hN hnN

end NeumannCosineAudit.NeumannCosine.Discrete.Eigenvalues

namespace NeumannCosineAudit.NeumannCosine.Discrete.Laplacian

/-- **The discrete eigenvalues are strictly increasing.** For `L ≠ 0`, `N ≥ 1` and
`n < k ≤ N`, `λ_n^N < λ_k^N` where `λ_n^N = 4/(L/N)² · sin²(nπ/(2N))`; in particular the
`N + 1` eigenvalues of the discrete Neumann Laplacian are distinct.
Library: `NeumannCosine.Discrete.Laplacian.discreteNeumannEigenvalue_lt_of_lt`, with
`discreteNeumannEigenvalue` and `discreteHalfAngle` unfolded. -/
theorem discreteNeumannEigenvalue_lt_of_lt (L : ℝ) (N n k : ℕ) (hL : L ≠ 0) (hN : 0 < N)
    (hnk : n < k) (hkN : k ≤ N) :
    4 / (L / (N : ℝ)) ^ 2 * Real.sin ((n : ℝ) * Real.pi / (2 * (N : ℝ))) ^ 2 <
      4 / (L / (N : ℝ)) ^ 2 * Real.sin ((k : ℝ) * Real.pi / (2 * (N : ℝ))) ^ 2 := by
  exact _root_.NeumannCosine.Discrete.Laplacian.discreteNeumannEigenvalue_lt_of_lt
    L N n k hL hN hnk hkN

/-- **The discrete cosines are linearly independent.** For `L ≠ 0` and `N ≥ 1`, the
`N + 1` grid functions `j ↦ cos(nπj/N)` on `{0, 1, …, N}`, `0 ≤ n ≤ N`, are linearly
independent over `ℝ`.
Library: `NeumannCosine.Discrete.Laplacian.discreteCosineModes_linearIndependent`, with
`GridFunction N = Fin (N + 1) → ℝ` and `discreteCosineMode` unfolded. -/
theorem discreteCosineModes_linearIndependent (L : ℝ) (N : ℕ) (hL : L ≠ 0) (hN : 0 < N) :
    LinearIndependent ℝ (fun n : Fin (N + 1) => fun j : Fin (N + 1) =>
      Real.cos (((n : ℕ) : ℝ) * Real.pi * ((j : ℕ) : ℝ) / (N : ℝ))) := by
  exact _root_.NeumannCosine.Discrete.Laplacian.discreteCosineModes_linearIndependent L N hL hN

end NeumannCosineAudit.NeumannCosine.Discrete.Laplacian
