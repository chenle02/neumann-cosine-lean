module
/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/

public import NeumannCosine.Basic

@[expose] public section

/-!
# Cosine projection of a source plus a divergence term

Let `R₁` vanish at `0` and `L`, and let `|R₀|, |R₁| ≤ B` on `[0, L]`.
Then the projection of `R₀ + R₁'` on the Neumann mode `cos (k π x / L)` obeys

  `|∫₀ᴸ (R₀ + R₁') cos(kπx/L) dx| ≤ (L + kπ) B`.

The source part gives `L B`. For the divergence part, integrate by parts:
the boundary terms vanish, and the result is at most `(kπ/L) · L B`.

* `abs_integral_source_add_deriv_mul_cos_le`: `R₁` is continuous on `[0, L]`
  and has derivative `dR₁` on `(0, L)`, with `dR₁` interval integrable.
* `abs_integral_source_add_deriv_mul_cos_le_deriv`: the same with `deriv R₁`.
* `abs_integral_source_add_deriv_mul_cos_le_of_absolutelyContinuous`: `R₁` is
  absolutely continuous on `[0, L]`, and `deriv R₁` (defined almost everywhere)
  replaces `dR₁`.
-/

namespace NeumannCosine.DivergenceFormProjection

open Real Set MeasureTheory intervalIntegral

/-- Integration by parts against the cosine mode, with vanishing boundary values:
`∫₀ᴸ dR₁ cos(ωx) dx = ω ∫₀ᴸ R₁ sin(ωx) dx`, `ω = kπ/L`. -/
theorem integral_deriv_mul_cos {L : ℝ} (hL : 0 < L) (k : ℕ) {R1 dR1 : ℝ → ℝ}
    (hR1c : ContinuousOn R1 (Icc 0 L)) (hR1d : ∀ x ∈ Ioo 0 L, HasDerivAt R1 (dR1 x) x)
    (hdR1 : IntervalIntegrable dR1 volume 0 L) (h0 : R1 0 = 0) (hL0 : R1 L = 0) :
    ∫ x in (0 : ℝ)..L, dR1 x * cos (freq L k * x) =
      freq L k * ∫ x in (0 : ℝ)..L, R1 x * sin (freq L k * x) := by
  set ω := freq L k
  have hle : (0 : ℝ) ≤ L := hL.le
  have hcos_cont : ContinuousOn (fun x => cos (ω * x)) (uIcc 0 L) := by fun_prop
  have hR1c' : ContinuousOn R1 (uIcc 0 L) := by rwa [uIcc_of_le hle]
  have hcos_d : ∀ x ∈ Ioo (min 0 L) (max 0 L),
      HasDerivAt (fun x => cos (ω * x)) (-sin (ω * x) * ω) x := by
    intro x _
    have := ((hasDerivAt_id x).const_mul ω).cos
    simpa [mul_comm] using this
  have hR1d' : ∀ x ∈ Ioo (min 0 L) (max 0 L), HasDerivAt R1 (dR1 x) x := by
    intro x hx
    rw [min_eq_left hle, max_eq_right hle] at hx
    exact hR1d x hx
  have hsin_int : IntervalIntegrable (fun x => -sin (ω * x) * ω) volume 0 L :=
    (by fun_prop : Continuous fun x => -sin (ω * x) * ω).intervalIntegrable 0 L
  -- `∫ cos · dR₁ = cos L R₁ L - cos 0 R₁ 0 - ∫ (-ω sin) R₁`.
  have hibp := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hcos_cont hR1c' hcos_d hR1d'
    hsin_int hdR1
  have hswap : ∫ x in (0 : ℝ)..L, dR1 x * cos (ω * x) =
      ∫ x in (0 : ℝ)..L, cos (ω * x) * dR1 x := by
    congr 1; ext x; ring
  rw [hswap, hibp, h0, hL0]
  have : ∫ x in (0 : ℝ)..L, -sin (ω * x) * ω * R1 x =
      -(ω * ∫ x in (0 : ℝ)..L, R1 x * sin (ω * x)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    congr 1; ext x; ring
  rw [this]; ring

/-- `|∫₀ᴸ f| ≤ L B` when `|f| ≤ B` on `[0, L]`. -/
theorem abs_integral_le_of_abs_le {L B : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf : ∀ x ∈ Icc 0 L, |f x| ≤ B) : |∫ x in (0 : ℝ)..L, f x| ≤ L * B := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := L) (C := B)
    (f := f) (fun x hx => by
      rw [uIoc_of_le hL.le] at hx
      simpa [Real.norm_eq_abs] using hf x (Ioc_subset_Icc_self hx))
  simpa [Real.norm_eq_abs, abs_of_pos hL, mul_comm] using h

/-- The estimate shared by the two integration-by-parts forms: once
`∫₀ᴸ dR₁ cos = ω ∫₀ᴸ R₁ sin`, the projection is at most `(L + kπ) B`. -/
theorem abs_integral_add_mul_cos_le_of_ibp {L B : ℝ} (hL : 0 < L) (k : ℕ) {R0 R1 dR1 : ℝ → ℝ}
    (hR0 : IntervalIntegrable R0 volume 0 L) (hdR1 : IntervalIntegrable dR1 volume 0 L)
    (hibp : ∫ x in (0 : ℝ)..L, dR1 x * cos (freq L k * x) =
      freq L k * ∫ x in (0 : ℝ)..L, R1 x * sin (freq L k * x))
    (hB0 : ∀ x ∈ Icc 0 L, |R0 x| ≤ B) (hB1 : ∀ x ∈ Icc 0 L, |R1 x| ≤ B) :
    |∫ x in (0 : ℝ)..L, (R0 x + dR1 x) * cos (k * π * x / L)| ≤ (L + k * π) * B := by
  set ω := freq L k with hω
  have hcosc : Continuous fun x => cos (ω * x) := by fun_prop
  have hsplit : ∫ x in (0 : ℝ)..L, (R0 x + dR1 x) * cos (k * π * x / L) =
      (∫ x in (0 : ℝ)..L, R0 x * cos (ω * x)) + ∫ x in (0 : ℝ)..L, dR1 x * cos (ω * x) := by
    rw [← intervalIntegral.integral_add (hR0.mul_continuousOn hcosc.continuousOn)
      (hdR1.mul_continuousOn hcosc.continuousOn)]
    congr 1; ext x; rw [hω, cos_freq_mul]; ring
  rw [hsplit, hibp]
  have h1 : |∫ x in (0 : ℝ)..L, R0 x * cos (ω * x)| ≤ L * B :=
    abs_integral_le_of_abs_le hL fun x hx => by
      rw [abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)).trans (hB0 x hx)
  have h2 : |∫ x in (0 : ℝ)..L, R1 x * sin (ω * x)| ≤ L * B :=
    abs_integral_le_of_abs_le hL fun x hx => by
      rw [abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) (abs_sin_le_one _)).trans (hB1 x hx)
  have hω0 : 0 ≤ ω := freq_nonneg hL k
  calc |(∫ x in (0 : ℝ)..L, R0 x * cos (ω * x)) + ω * ∫ x in (0 : ℝ)..L, R1 x * sin (ω * x)|
      ≤ |∫ x in (0 : ℝ)..L, R0 x * cos (ω * x)| + ω * |∫ x in (0 : ℝ)..L, R1 x * sin (ω * x)| := by
        rw [← abs_of_nonneg hω0, ← abs_mul, abs_of_nonneg hω0]; exact abs_add_le _ _
    _ ≤ L * B + ω * (L * B) := by gcongr
    _ = (L + k * π) * B := by rw [← freq_mul_length hL k]; ring

/-- **Projection bound** (differentiable `R₁`). For `L > 0` and `k : ℕ`, let `R₁` be
continuous on `[0, L]` with derivative `dR₁` on `(0, L)`, `dR₁` interval integrable,
`R₁ 0 = R₁ L = 0`, and let `R₀` be interval integrable, with `|R₀|, |R₁| ≤ B` on `[0, L]`. Then
`|∫₀ᴸ (R₀ + dR₁) cos(kπx/L) dx| ≤ (L + kπ) B`. -/
theorem abs_integral_source_add_deriv_mul_cos_le {L B : ℝ} (hL : 0 < L) (k : ℕ) {R0 R1 dR1 : ℝ → ℝ}
    (hR0 : IntervalIntegrable R0 volume 0 L)
    (hR1c : ContinuousOn R1 (Icc 0 L)) (hR1d : ∀ x ∈ Ioo 0 L, HasDerivAt R1 (dR1 x) x)
    (hdR1 : IntervalIntegrable dR1 volume 0 L) (h0 : R1 0 = 0) (hL0 : R1 L = 0)
    (hB0 : ∀ x ∈ Icc 0 L, |R0 x| ≤ B) (hB1 : ∀ x ∈ Icc 0 L, |R1 x| ≤ B) :
    |∫ x in (0 : ℝ)..L, (R0 x + dR1 x) * cos (k * π * x / L)| ≤ (L + k * π) * B :=
  abs_integral_add_mul_cos_le_of_ibp hL k hR0 hdR1 (integral_deriv_mul_cos hL k hR1c hR1d hdR1 h0 hL0)
    hB0 hB1

/-- **Projection bound** (`deriv` form). As `abs_integral_source_add_deriv_mul_cos_le`, with
`R₁` differentiable on `(0, L)` and its derivative written `deriv R₁`. -/
theorem abs_integral_source_add_deriv_mul_cos_le_deriv {L B : ℝ} (hL : 0 < L) (k : ℕ) {R0 R1 : ℝ → ℝ}
    (hR0 : IntervalIntegrable R0 volume 0 L)
    (hR1c : ContinuousOn R1 (Icc 0 L)) (hR1d : ∀ x ∈ Ioo 0 L, DifferentiableAt ℝ R1 x)
    (hdR1 : IntervalIntegrable (deriv R1) volume 0 L) (h0 : R1 0 = 0) (hL0 : R1 L = 0)
    (hB0 : ∀ x ∈ Icc 0 L, |R0 x| ≤ B) (hB1 : ∀ x ∈ Icc 0 L, |R1 x| ≤ B) :
    |∫ x in (0 : ℝ)..L, (R0 x + deriv R1 x) * cos (k * π * x / L)| ≤ (L + k * π) * B :=
  abs_integral_source_add_deriv_mul_cos_le hL k hR0 hR1c (fun x hx => (hR1d x hx).hasDerivAt) hdR1 h0 hL0
    hB0 hB1

/-- **Projection bound** (absolutely continuous `R₁`). As `abs_integral_source_add_deriv_mul_cos_le`,
with `R₁` absolutely continuous on `[0, L]` and its derivative `deriv R₁`, which exists
almost everywhere and is integrable (Mathlib's `AbsolutelyContinuousOnInterval`). -/
theorem abs_integral_source_add_deriv_mul_cos_le_of_absolutelyContinuous {L B : ℝ} (hL : 0 < L) (k : ℕ)
    {R0 R1 : ℝ → ℝ} (hR0 : IntervalIntegrable R0 volume 0 L)
    (hR1 : AbsolutelyContinuousOnInterval R1 0 L) (h0 : R1 0 = 0) (hL0 : R1 L = 0)
    (hB0 : ∀ x ∈ Icc 0 L, |R0 x| ≤ B) (hB1 : ∀ x ∈ Icc 0 L, |R1 x| ≤ B) :
    |∫ x in (0 : ℝ)..L, (R0 x + deriv R1 x) * cos (k * π * x / L)| ≤ (L + k * π) * B := by
  set ω := freq L k
  have hcos : AbsolutelyContinuousOnInterval (fun x => cos (ω * x)) 0 L :=
    ContDiffOn.absolutelyContinuousOnInterval (by fun_prop)
  have hibp : ∫ x in (0 : ℝ)..L, deriv R1 x * cos (ω * x) =
      ω * ∫ x in (0 : ℝ)..L, R1 x * sin (ω * x) := by
    have h := hcos.integral_mul_deriv_eq_deriv_mul hR1
    have hd : ∀ x, deriv (fun x => cos (ω * x)) x = -sin (ω * x) * ω := by
      intro x
      have := ((hasDerivAt_id x).const_mul ω).cos
      simp [mul_comm]
    simp_rw [hd, h0, hL0] at h
    have hswap : ∫ x in (0 : ℝ)..L, deriv R1 x * cos (ω * x) =
        ∫ x in (0 : ℝ)..L, cos (ω * x) * deriv R1 x := by
      congr 1; ext x; ring
    rw [hswap, h]
    have : ∫ x in (0 : ℝ)..L, -sin (ω * x) * ω * R1 x =
        -(ω * ∫ x in (0 : ℝ)..L, R1 x * sin (ω * x)) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
      congr 1; ext x; ring
    rw [this]; ring
  exact abs_integral_add_mul_cos_le_of_ibp hL k hR0 hR1.intervalIntegrable_deriv hibp hB0 hB1

/-- Example: the hypotheses of `abs_integral_source_add_deriv_mul_cos_le` hold for `R₀ = 1`,
`R₁ x = sin(πx/L)` (vanishing at `0` and `L`) with `B = 1`, so the bound is not vacuous. -/
theorem abs_integral_source_add_deriv_mul_cos_le_example {L : ℝ} (hL : 0 < L) (k : ℕ) :
    |∫ x in (0 : ℝ)..L, ((fun _ => (1 : ℝ)) x + (fun x => π / L * cos (π / L * x)) x) *
        cos (k * π * x / L)| ≤ (L + k * π) * 1 := by
  refine abs_integral_source_add_deriv_mul_cos_le (R1 := fun x => sin (π / L * x)) hL k
    (by simp) (by fun_prop) (fun x _ => ?_)
    ((by fun_prop : Continuous fun x => π / L * cos (π / L * x)).intervalIntegrable 0 L)
    (by simp) ?_ (fun x _ => by simp)
    (fun x _ => abs_sin_le_one _)
  · have := ((hasDerivAt_id x).const_mul (π / L)).sin
    simpa [mul_comm] using this
  · show sin (π / L * L) = 0
    rw [div_mul_cancel₀ π hL.ne', sin_pi]

end NeumannCosine.DivergenceFormProjection
