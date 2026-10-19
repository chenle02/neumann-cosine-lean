module
/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/

public import NeumannCosine.Sobolev.WeakDerivative
public import NeumannCosine.Coefficients

@[expose] public section

/-!
# `H²(0,L)` with Neumann data

Let `w ∈ H²(0,L)` with `w_x(0) = w_x(L) = 0`. We show that `w` has a
representative in the class `NeumannW21` of `NeumannCosine.Coefficients`.
Hence the cosine coefficients of `w` are absolutely summable, and the cosine
series of `w` converges at every point of `[0, L]`.

## Definitions

* `H2 L w w₁ w₂`: `w, w₁, w₂ ∈ L²(0,L)`, `w₁` is the weak derivative of `w` and
  `w₂` that of `w₁` (no integrability is assumed beyond `L²`).
* `NeumannTrace L w₁`: `w₁` has a representative continuous on `[0,L]`
  vanishing at `0` and `L` (the trace condition `w_x(0) = w_x(L) = 0`; the
  continuous representative is unique, `eqOn_of_ae_eq_continuousOn`).

## Main results

* `H2.exists_neumannW21`: such a `w` has a representative `W` with
  `NeumannW21 L W W'`, `W = w` and `W' = w₁` a.e. on `(0,L)`.
* `H2.summable_norm_cosineCoeff`, `H2.hasSum_cosineCoeff`: the cosine
  coefficients of `w` are absolutely summable, and the cosine series converges
  to a continuous representative of `w` on `[0,L]`.
-/

set_option autoImplicit false

namespace NeumannCosine.Sobolev.H2Neumann

open MeasureTheory Set Real Filter Topology Function
open scoped Interval ContDiff
open NeumannCosine.Sobolev.WeakDerivative

noncomputable section

/-! ### `H²(0,L)` with Neumann data -/

/-- `w ∈ H²(0,L)` with weak derivatives `w₁ = w_x`, `w₂ = w_{xx}`:
`w, w₁, w₂ ∈ L²(0,L)`, `∫₀ᴸ w φ' = -∫₀ᴸ w₁ φ` and `∫₀ᴸ w₁ φ' = -∫₀ᴸ w₂ φ` for
every `φ ∈ C_c^∞(0,L)`. -/
structure H2 (L : ℝ) (w w₁ w₂ : ℝ → ℝ) : Prop where
  /-- `w ∈ L²(0,L)`. -/
  memLp : MemLp w 2 (volume.restrict (Ioo 0 L))
  /-- `w_x ∈ L²(0,L)`. -/
  memLp_deriv : MemLp w₁ 2 (volume.restrict (Ioo 0 L))
  /-- `w_{xx} ∈ L²(0,L)`. -/
  memLp_deriv2 : MemLp w₂ 2 (volume.restrict (Ioo 0 L))
  /-- `w₁` is the weak derivative of `w`. -/
  weak_deriv : ∀ φ : ℝ → ℝ, IsTestFunction L φ →
    ∫ x in (0 : ℝ)..L, w x * deriv φ x = -∫ x in (0 : ℝ)..L, w₁ x * φ x
  /-- `w₂` is the weak derivative of `w₁`. -/
  weak_deriv2 : ∀ φ : ℝ → ℝ, IsTestFunction L φ →
    ∫ x in (0 : ℝ)..L, w₁ x * deriv φ x = -∫ x in (0 : ℝ)..L, w₂ x * φ x

/-- The Neumann trace condition `w_x(0) = w_x(L) = 0`, stated on
the continuous representative of `w₁ = w_x`: some `V` continuous on `[0,L]`
agrees with `w₁` a.e. on `(0,L)` and vanishes at both endpoints.  The
representative is unique (`eqOn_of_ae_eq_continuousOn`), so the existential
is the trace condition itself. -/
def NeumannTrace (L : ℝ) (w₁ : ℝ → ℝ) : Prop :=
  ∃ V : ℝ → ℝ, ContinuousOn V (Icc 0 L) ∧ (∀ᵐ x, x ∈ Ioo 0 L → w₁ x = V x) ∧
    V 0 = 0 ∧ V L = 0

/-- `H²(0,L) ⊆ W^{1,1}(0,L)`: the first weak derivative. -/
theorem H2.hasWeakDeriv {L : ℝ} (hL : 0 < L) {w w₁ w₂ : ℝ → ℝ} (h : H2 L w w₁ w₂) :
    HasWeakDeriv L w w₁ :=
  ⟨intervalIntegrable_of_memLp hL h.memLp, intervalIntegrable_of_memLp hL h.memLp_deriv,
    h.weak_deriv⟩

/-- `H²(0,L)`: the second weak derivative, as a `W^{1,1}` statement for `w₁`. -/
theorem H2.hasWeakDeriv2 {L : ℝ} (hL : 0 < L) {w w₁ w₂ : ℝ → ℝ} (h : H2 L w w₁ w₂) :
    HasWeakDeriv L w₁ w₂ :=
  ⟨intervalIntegrable_of_memLp hL h.memLp_deriv,
    intervalIntegrable_of_memLp hL h.memLp_deriv2, h.weak_deriv2⟩

/-- **`H²` with Neumann data lies in the Neumann class.**  If
`w ∈ H²(0,L)` (weak derivatives `w₁, w₂`) satisfies the Neumann trace condition
`w_x(0) = w_x(L) = 0`, then `w` has a representative `W` with
`NeumannW21 L W W'`, where `W = w` and `W' = w₁` a.e. on `(0,L)`. -/
theorem H2.exists_neumannW21 {L : ℝ} (hL : 0 < L) {w w₁ w₂ : ℝ → ℝ}
    (h : H2 L w w₁ w₂) (hN : NeumannTrace L w₁) :
    ∃ W W' : ℝ → ℝ, Coefficients.NeumannW21 L W W' ∧
      (∀ᵐ x, x ∈ Ioo 0 L → w x = W x) ∧ (∀ᵐ x, x ∈ Ioo 0 L → w₁ x = W' x) := by
  obtain ⟨V, hVc, hVae, hV0, hVL⟩ := hN
  obtain ⟨c₁, hc₁, hac₁, -⟩ := (h.hasWeakDeriv2 hL).ae_eq_primitive hL
  have hV1c : ContinuousOn (fun x => c₁ + ∫ t in (0 : ℝ)..x, w₂ t) (Icc 0 L) := by
    simpa [uIcc_of_le hL.le] using hac₁.continuousOn
  have hEq : EqOn (fun x => c₁ + ∫ t in (0 : ℝ)..x, w₂ t) V (Icc 0 L) := by
    refine eqOn_of_ae_eq_continuousOn hL hV1c hVc ?_
    filter_upwards [hc₁, hVae] with x h1 h2 hx
    rw [← h1 hx, h2 hx]
  have hVac : AbsolutelyContinuousOnInterval V 0 L :=
    hac₁.congr (by rwa [uIcc_of_le hL.le])
  obtain ⟨c₀, hc₀, -, -⟩ := (h.hasWeakDeriv hL).ae_eq_primitive hL
  have hVi : ∀ x ∈ Icc 0 L, IntervalIntegrable V volume 0 x := fun x hx =>
    (hVc.mono (by rw [uIcc_of_le hx.1]; exact Icc_subset_Icc_right hx.2)).intervalIntegrable
  refine ⟨fun x => c₀ + ∫ t in (0 : ℝ)..x, V t, V, ⟨?_, ?_, hVac, hV0, hVL⟩, ?_, hVae⟩
  · exact absolutelyContinuousOnInterval_const_add
      ((hVi L ⟨hL.le, le_rfl⟩).absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)
      c₀
  · intro x hx
    exact (intervalIntegral.integral_hasDerivAt_right (hVi x (Ioo_subset_Icc_self hx))
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
        (hVc.mono Ioo_subset_Icc_self) x hx)
      (hVc.continuousAt (Icc_mem_nhds hx.1 hx.2))).const_add c₀
  · filter_upwards [hc₀] with x h0 hx
    rw [h0 hx]
    congr 1
    refine integral_congr_ae_Ioo hx.1.le ?_
    filter_upwards [hVae] with t ht htx
    exact ht ⟨htx.1, htx.2.trans hx.2⟩

/-- The cosine coefficients only depend on the a.e. class on `(0,L)`. -/
theorem cosineCoeff_congr_ae {L : ℝ} (hL : 0 < L) {w W : ℝ → ℝ}
    (h : ∀ᵐ x, x ∈ Ioo 0 L → w x = W x) (k : ℕ) :
    Coefficients.cosineCoeff L w k = Coefficients.cosineCoeff L W k := by
  unfold Coefficients.cosineCoeff
  congr 1
  refine integral_congr_ae_Ioo hL.le ?_
  filter_upwards [h] with x hx hxI
  rw [hx hxI]

/-- **Summable coefficients.**  For `w ∈ H²(0,L)` with Neumann data, the cosine
coefficients are absolutely summable: `{w_n} ∈ ℓ¹(ℕ₀)`. -/
theorem H2.summable_norm_cosineCoeff {L : ℝ} (hL : 0 < L) {w w₁ w₂ : ℝ → ℝ}
    (h : H2 L w w₁ w₂) (hN : NeumannTrace L w₁) :
    Summable fun k => ‖Coefficients.cosineCoeff L w k‖ := by
  obtain ⟨W, W', hW, hwW, -⟩ := h.exists_neumannW21 hL hN
  simpa only [cosineCoeff_congr_ae hL hwW] using
    Coefficients.summable_norm_cosineCoeff L hL hW

/-- **Cosine expansion.**  For `w ∈ H²(0,L)` with Neumann data there is a
representative `W`, continuous on `[0,L]` and equal to `w` a.e. on `(0,L)`, with
`W(x) = ∑_{n ≥ 0} w_n cos(n π x / L)` for every `x ∈ [0,L]`, where `w_n` are the
cosine coefficients of `w`. -/
theorem H2.hasSum_cosineCoeff {L : ℝ} (hL : 0 < L) {w w₁ w₂ : ℝ → ℝ}
    (h : H2 L w w₁ w₂) (hN : NeumannTrace L w₁) :
    ∃ W : ℝ → ℝ, (∀ᵐ x, x ∈ Ioo 0 L → w x = W x) ∧ ContinuousOn W (Icc 0 L) ∧
      ∀ x ∈ Icc 0 L, HasSum (fun k : ℕ => Coefficients.cosineCoeff L w k *
        Real.cos ((k : ℝ) * Real.pi * x / L)) (W x) := by
  obtain ⟨W, W', hW, hwW, -⟩ := h.exists_neumannW21 hL hN
  refine ⟨W, hwW, by simpa [uIcc_of_le hL.le] using hW.ac.continuousOn, fun x hx => ?_⟩
  simpa only [cosineCoeff_congr_ae hL hwW] using
    Coefficients.hasSum_cosineCoeff L hL hW hx

end

end NeumannCosine.Sobolev.H2Neumann
