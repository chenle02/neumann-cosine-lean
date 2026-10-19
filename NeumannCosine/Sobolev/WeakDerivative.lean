module
/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/

public import Mathlib

@[expose] public section

/-!
# Weak derivatives on an interval

Mathlib has no Sobolev spaces. This file sets up one-dimensional weak
derivatives on `(0, L)` and proves two classical facts.

## Definitions

* `IsTestFunction L φ`: `φ ∈ C_c^∞(0,L)`, i.e. `φ` is smooth, compactly
  supported, and `tsupport φ ⊆ (0,L)`.
* `HasWeakDeriv L w g`: `w, g ∈ L¹(0,L)` and `∫₀ᴸ w φ' = -∫₀ᴸ g φ` for every
  `φ ∈ C_c^∞(0,L)`.

## Main results

* `ae_eq_const_of_integral_mul_deriv_eq_zero` (du Bois-Reymond): if
  `h ∈ L¹(0,L)` and `∫₀ᴸ h φ' = 0` for all `φ ∈ C_c^∞(0,L)`, then `h` is a.e.
  constant on `(0,L)`.
* `HasWeakDeriv.ae_eq_primitive` (`W^{1,1}` ⇒ absolutely continuous): if `g` is
  a weak derivative of `w`, then `w = c + ∫₀ˣ g` a.e. on `(0,L)`, and this
  representative is absolutely continuous with derivative `g` a.e.
* `eqOn_of_ae_eq_continuousOn`: two functions continuous on `[0,L]` that agree
  a.e. on `(0,L)` agree on `[0,L]`.
-/

set_option autoImplicit false

namespace NeumannCosine.Sobolev.WeakDerivative

open MeasureTheory Set Real Filter Topology Function
open scoped Interval ContDiff

noncomputable section

/-- `φ ∈ C_c^∞(0,L)`: smooth, compactly supported, with `tsupport φ ⊆ (0,L)`. -/
def IsTestFunction (L : ℝ) (φ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ioo 0 L

/-- `g` is a weak derivative of `w` on `(0,L)` (both in `L¹(0,L)`):
`∫₀ᴸ w φ' = -∫₀ᴸ g φ` for every `φ ∈ C_c^∞(0,L)`. -/
structure HasWeakDeriv (L : ℝ) (w g : ℝ → ℝ) : Prop where
  /-- `w ∈ L¹(0,L)`. -/
  integrable : IntervalIntegrable w volume 0 L
  /-- `g ∈ L¹(0,L)`. -/
  integrable_deriv : IntervalIntegrable g volume 0 L
  /-- The integration-by-parts identity against test functions. -/
  integral_eq : ∀ φ : ℝ → ℝ, IsTestFunction L φ →
    ∫ x in (0 : ℝ)..L, w x * deriv φ x = -∫ x in (0 : ℝ)..L, g x * φ x

namespace IsTestFunction

variable {L : ℝ} {φ : ℝ → ℝ}

/-- A test function is continuous. -/
theorem continuous (hφ : IsTestFunction L φ) : Continuous φ :=
  hφ.1.continuous

/-- A test function vanishes off `(0,L)`. -/
theorem eq_zero_of_notMem (hφ : IsTestFunction L φ) {x : ℝ} (hx : x ∉ Ioo 0 L) :
    φ x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx (hφ.2.2 h)

/-- The derivative `φ'` of a test function is continuous. -/
theorem continuous_deriv (hφ : IsTestFunction L φ) : Continuous (deriv φ) :=
  (contDiff_infty_iff_deriv.mp hφ.1).2.continuous

/-- An integral over `ℝ` of `φ · F` equals the integral over `(0,L)`. -/
theorem integral_mul_eq (hφ : IsTestFunction L φ) (F : ℝ → ℝ) :
    ∫ x, φ x * F x = ∫ x in (0 : ℝ)..L, φ x * F x := by
  symm
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro x hx
  have : φ x ≠ 0 := fun h => hx (by simp [h])
  have hx' := hφ.2.2 (subset_tsupport φ this)
  exact ⟨hx'.1, hx'.2.le⟩

end IsTestFunction

/-- A compact subset of `(0,L)` lies in some `[a,b] ⊆ (0,L)`. -/
theorem exists_Icc_of_isCompact {L : ℝ} (hL : 0 < L) {K : Set ℝ} (hK : IsCompact K)
    (hKL : K ⊆ Ioo 0 L) : ∃ a b, 0 < a ∧ b < L ∧ K ⊆ Icc a b := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨L / 2, L / 2, by positivity, by linarith, empty_subset _⟩
  refine ⟨sInf K, sSup K, (hKL (hK.sInf_mem hne)).1, (hKL (hK.sSup_mem hne)).2, ?_⟩
  intro x hx
  exact ⟨csInf_le hK.bddBelow hx, le_csSup hK.bddAbove hx⟩

/-- The primitive of a smooth function supported in `[a,b] ⊆ (0,L)` with zero
total integral is a test function. -/
theorem isTestFunction_primitive {L : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {a b : ℝ}
    (ha : 0 < a) (hb : b < L) (hfs : support f ⊆ Icc a b) (hint : ∫ x, f x = 0) :
    IsTestFunction L (fun x => ∫ t in (0 : ℝ)..x, f t) ∧
      deriv (fun x => ∫ t in (0 : ℝ)..x, f t) = f := by
  have hderiv : ∀ x, HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, f t) (f x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hf.continuous.intervalIntegrable _ _)
      (hf.continuous.stronglyMeasurableAtFilter _ _) hf.continuous.continuousAt
  have hd : deriv (fun x => ∫ t in (0 : ℝ)..x, f t) = f := funext fun x => (hderiv x).deriv
  have hsupp : support (fun x => ∫ t in (0 : ℝ)..x, f t) ⊆ Icc a b := by
    intro x hx
    by_contra hxab
    apply hx
    rcases lt_or_ge x a with hxa | hxa
    · have : EqOn f 0 (uIcc 0 x) := by
        intro t ht
        have : t < a := lt_of_le_of_lt ht.2 (max_lt ha hxa)
        by_contra hft
        exact absurd (hfs hft).1 (not_le.mpr this)
      simp [intervalIntegral.integral_congr this]
    · have hxb : b < x := by
        by_contra h
        exact hxab ⟨hxa, not_lt.mp h⟩
      show ∫ t in (0 : ℝ)..x, f t = 0
      rw [intervalIntegral.integral_eq_integral_of_support_subset, hint]
      intro t ht
      have := hfs ht
      exact ⟨by linarith [this.1], by linarith [this.2]⟩
  refine ⟨⟨contDiff_infty_iff_deriv.mpr ⟨fun x => (hderiv x).differentiableAt, by rw [hd]; exact hf⟩,
    ?_, ?_⟩, hd⟩
  · exact HasCompactSupport.intro isCompact_Icc fun x hx => by
      by_contra h
      exact hx (hsupp h)
  · calc tsupport (fun x => ∫ t in (0 : ℝ)..x, f t) ⊆ Icc a b :=
          closure_minimal hsupp isClosed_Icc
      _ ⊆ Ioo 0 L := Icc_subset_Ioo ha hb

/-- **du Bois-Reymond lemma.**  If `h ∈ L¹(0,L)` and `∫₀ᴸ h φ' = 0` for every
`φ ∈ C_c^∞(0,L)`, then `h` is a.e. equal to a constant on `(0,L)`. -/
theorem ae_eq_const_of_integral_mul_deriv_eq_zero {L : ℝ} (hL : 0 < L) {h : ℝ → ℝ}
    (hh : IntervalIntegrable h volume 0 L)
    (H : ∀ φ : ℝ → ℝ, IsTestFunction L φ → ∫ x in (0 : ℝ)..L, h x * deriv φ x = 0) :
    ∃ c : ℝ, ∀ᵐ x, x ∈ Ioo 0 L → h x = c := by
  let β : ContDiffBump (L / 2) := ⟨L / 8, L / 4, by positivity, by linarith⟩
  set ψ₀ := β.normed volume with hψ₀def
  have hψ₀ : IsTestFunction L ψ₀ := by
    refine ⟨β.contDiff_normed, β.hasCompactSupport_normed, ?_⟩
    rw [β.tsupport_normed_eq]
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
    have h1 : -(L / 4) ≤ x - L / 2 := hx.1
    have h2 : x - L / 2 ≤ L / 4 := hx.2
    constructor <;> linarith
  have hψ₀int : ∫ x, ψ₀ x = 1 := β.integral_normed
  set c := ∫ x in (0 : ℝ)..L, h x * ψ₀ x with hc
  refine ⟨c, ?_⟩
  have key : ∀ ψ : ℝ → ℝ, IsTestFunction L ψ →
      ∫ x in (0 : ℝ)..L, h x * ψ x = c * ∫ x, ψ x := by
    intro ψ hψ
    set s := ∫ x, ψ x
    let f : ℝ → ℝ := fun x => ψ x - s * ψ₀ x
    have hfC : ContDiff ℝ ∞ f := hψ.1.sub (contDiff_const.mul hψ₀.1)
    obtain ⟨a, b, ha, hb, hab⟩ := exists_Icc_of_isCompact hL (hψ.2.1.union hψ₀.2.1)
      (union_subset hψ.2.2 hψ₀.2.2)
    have hfs : support f ⊆ Icc a b := by
      intro x hx
      apply hab
      by_contra hn
      rw [mem_union, not_or] at hn
      apply hx
      simp [f, image_eq_zero_of_notMem_tsupport hn.1, image_eq_zero_of_notMem_tsupport hn.2]
    have hint : ∫ x, f x = 0 := by
      have i1 : Integrable ψ := hψ.continuous.integrable_of_hasCompactSupport hψ.2.1
      have i2 : Integrable ψ₀ := hψ₀.continuous.integrable_of_hasCompactSupport hψ₀.2.1
      simp only [f]
      rw [integral_sub i1 (i2.const_mul s), integral_const_mul, hψ₀int]
      ring
    obtain ⟨hφ, hd⟩ := isTestFunction_primitive hfC ha hb hfs hint
    have hH := H _ hφ
    rw [hd] at hH
    have i3 : IntervalIntegrable (fun x => h x * ψ x) volume 0 L :=
      hh.mul_continuousOn hψ.continuous.continuousOn
    have i4 : IntervalIntegrable (fun x => h x * (s * ψ₀ x)) volume 0 L :=
      hh.mul_continuousOn (continuous_const.mul hψ₀.continuous).continuousOn
    simp only [f, mul_sub] at hH
    rw [intervalIntegral.integral_sub i3 i4] at hH
    have e : ∫ x in (0 : ℝ)..L, h x * (s * ψ₀ x) = s * c := by
      rw [hc, ← intervalIntegral.integral_const_mul]
      congr 1
      ext x
      ring
    rw [e] at hH
    linarith
  have hIoc : IntegrableOn (fun x => h x - c) (Ioc 0 L) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le).mp (hh.sub intervalIntegrable_const)
  have hloc : LocallyIntegrableOn (fun x => h x - c) (Ioo 0 L) volume :=
    (hIoc.mono_set Ioo_subset_Ioc_self).locallyIntegrableOn
  have hzero := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc ?_
  · filter_upwards [hzero] with x hx hxU using sub_eq_zero.mp (hx hxU)
  intro g hg hgc hgs
  have hgT : IsTestFunction L g := ⟨hg, hgc, hgs⟩
  simp only [smul_eq_mul]
  rw [hgT.integral_mul_eq]
  have i5 : IntervalIntegrable (fun x => h x * g x) volume 0 L :=
    hh.mul_continuousOn hgT.continuous.continuousOn
  have i6 : IntervalIntegrable (fun x => c * g x) volume 0 L :=
    (continuous_const.mul hgT.continuous).intervalIntegrable _ _
  have e1 : ∫ x in (0 : ℝ)..L, g x * (h x - c) =
      (∫ x in (0 : ℝ)..L, h x * g x) - c * ∫ x in (0 : ℝ)..L, g x := by
    calc ∫ x in (0 : ℝ)..L, g x * (h x - c)
        = ∫ x in (0 : ℝ)..L, (h x * g x - c * g x) :=
          intervalIntegral.integral_congr fun x _ => by ring
      _ = (∫ x in (0 : ℝ)..L, h x * g x) - ∫ x in (0 : ℝ)..L, c * g x :=
          intervalIntegral.integral_sub i5 i6
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  have e2 : ∫ x, g x = ∫ x in (0 : ℝ)..L, g x := by
    simpa using hgT.integral_mul_eq (fun _ => 1)
  have hk := key g hgT
  rw [e2] at hk
  rw [e1]
  linear_combination hk

/-- Constant shift of an absolutely continuous function. -/
theorem absolutelyContinuousOnInterval_const_add {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (c : ℝ) :
    AbsolutelyContinuousOnInterval (fun x => c + f x) a b :=
  (contDiffOn_const (c := c)).absolutelyContinuousOnInterval.add hf

/-- **`W^{1,1}(0,L)` functions are absolutely continuous.**  If `g ∈ L¹(0,L)`
is a weak derivative of `w ∈ L¹(0,L)`, then for some constant `c`,
`w(x) = c + ∫₀ˣ g` for a.e. `x ∈ (0,L)`; this representative is absolutely
continuous on `[0,L]` and has derivative `g(x)` at a.e. `x ∈ [0,L]`. -/
theorem HasWeakDeriv.ae_eq_primitive {L : ℝ} (hL : 0 < L) {w g : ℝ → ℝ}
    (h : HasWeakDeriv L w g) :
    ∃ c : ℝ, (∀ᵐ x, x ∈ Ioo 0 L → w x = c + ∫ t in (0 : ℝ)..x, g t) ∧
      AbsolutelyContinuousOnInterval (fun x => c + ∫ t in (0 : ℝ)..x, g t) 0 L ∧
      ∀ᵐ x, x ∈ Icc 0 L → HasDerivAt (fun x => c + ∫ t in (0 : ℝ)..x, g t) (g x) x := by
  set G : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, g t with hG
  have hGac : AbsolutelyContinuousOnInterval G 0 L :=
    h.integrable_deriv.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hGd : ∀ᵐ x, x ∈ Icc 0 L → HasDerivAt G (g x) x := by
    filter_upwards [h.integrable_deriv.ae_hasDerivAt_integral] with x hx hxI
    rw [← uIcc_of_le hL.le] at hxI
    exact hx hxI 0 left_mem_uIcc
  have hGi : IntervalIntegrable G volume 0 L := hGac.continuousOn.intervalIntegrable
  have hGφ : ∀ φ : ℝ → ℝ, IsTestFunction L φ →
      ∫ x in (0 : ℝ)..L, G x * deriv φ x = -∫ x in (0 : ℝ)..L, g x * φ x := by
    intro φ hφ
    have hφac : AbsolutelyContinuousOnInterval φ 0 L :=
      (hφ.1.of_le (by norm_cast)).contDiffOn.absolutelyContinuousOnInterval
    rw [hGac.integral_mul_deriv_eq_deriv_mul hφac,
      hφ.eq_zero_of_notMem (x := 0) (by simp), hφ.eq_zero_of_notMem (x := L) (by simp)]
    simp only [mul_zero, sub_zero, zero_sub]
    congr 1
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hGd] with x hx hxI
    rw [uIoc_of_le hL.le] at hxI
    rw [(hx (Ioc_subset_Icc_self hxI)).deriv]
  have hH : ∀ φ : ℝ → ℝ, IsTestFunction L φ →
      ∫ x in (0 : ℝ)..L, (w - G) x * deriv φ x = 0 := by
    intro φ hφ
    have i1 := h.integrable.mul_continuousOn hφ.continuous_deriv.continuousOn
    have i2 := hGi.mul_continuousOn hφ.continuous_deriv.continuousOn
    simp only [Pi.sub_apply, sub_mul]
    rw [intervalIntegral.integral_sub i1 i2, h.integral_eq φ hφ, hGφ φ hφ]
    ring
  obtain ⟨c, hc⟩ := ae_eq_const_of_integral_mul_deriv_eq_zero hL (h.integrable.sub hGi) hH
  refine ⟨c, ?_, absolutelyContinuousOnInterval_const_add hGac c, ?_⟩
  · filter_upwards [hc] with x hx hxI
    have := hx hxI
    change w x = c + G x
    linarith
  · filter_upwards [hGd] with x hx hxI using (hx hxI).const_add c

/-- Uniqueness of the continuous representative: two functions continuous on
`[0,L]` that agree a.e. on `(0,L)` agree on all of `[0,L]`. -/
theorem eqOn_of_ae_eq_continuousOn {L : ℝ} (hL : 0 < L) {V V' : ℝ → ℝ}
    (hV : ContinuousOn V (Icc 0 L)) (hV' : ContinuousOn V' (Icc 0 L))
    (h : ∀ᵐ x, x ∈ Ioo 0 L → V x = V' x) : EqOn V V' (Icc 0 L) := by
  refine Measure.eqOn_Icc_of_ae_eq volume hL.ne ?_ hV hV'
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
  exact (ae_restrict_iff' measurableSet_Ioo).mpr h

/-- On a bounded interval `L² ⊆ L¹`. -/
theorem intervalIntegrable_of_memLp {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo 0 L))) : IntervalIntegrable f volume 0 L :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le hL.le).mpr (hf.integrable one_le_two)

/-- Interval integrals over `[a,b]` only see the values on `(a,b)` up to null
sets. -/
theorem integral_congr_ae_Ioo {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (h : ∀ᵐ x, x ∈ Ioo a b → f x = g x) :
    ∫ x in a..b, f x = ∫ x in a..b, g x := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_ae measurableSet_Ioo h

end

end NeumannCosine.Sobolev.WeakDerivative
