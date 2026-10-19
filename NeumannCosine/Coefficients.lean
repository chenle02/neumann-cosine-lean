module
/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/

public import NeumannCosine.ProductIdentities

@[expose] public section

/-!
# Cosine coefficients of functions with Neumann data

Let `w` be in `W^{2,1}(0,L)` with `w'(0) = w'(L) = 0`. We show that the cosine
coefficients of `w` are absolutely summable and that the cosine series of `w`
converges to `w` at every point of `[0, L]`.

## Regularity hypothesis

`NeumannW21 L w w'` packages, on `[0, L]`:

* `w` is absolutely continuous;
* `w` has (two-sided) derivative `w' x` at every interior point `x ∈ (0, L)`;
* `w'` is absolutely continuous (so `w'' := deriv w'` exists a.e. and is
  integrable, by Mathlib's FTC for absolutely continuous functions);
* the Neumann data `w'(0) = w'(L) = 0`.

This is the classical description of `W^{2,1}(0,L)` with Neumann data: in one
dimension every `w ∈ W^{2,1}(0,L)` has a representative which is `C¹` on
`[0, L]` with absolutely continuous derivative, and conversely.  Since `(0,L)`
is bounded, `H²(0,L) ⊂ W^{2,1}(0,L)` (Cauchy–Schwarz).  The file
`NeumannCosine.Sobolev.H2Neumann` proves that every `w ∈ H²(0,L)` with
`w_x(0) = w_x(L) = 0` has a representative in `NeumannW21`
(`H2.exists_neumannW21`), and applies the results below to `w`
(`H2.summable_norm_cosineCoeff`, `H2.hasSum_cosineCoeff`).  No `L²` bound on
`w''` is needed: integrability of `w''` already gives `|w_k| = O(k⁻²)`.

## Coefficient convention

`w_0 = (1/L) ∫₀ᴸ w`, and `w_k = (2/L) ∫₀ᴸ w(x) cos(k π x / L) dx` for `k ≥ 1`.

## Main results

* `cosineCoeff_eq_neg_mul_secondDeriv`: for `k ≥ 1`,
  `w_k = -(L/(kπ))² · (2/L) ∫₀ᴸ w''(x) cos(k π x / L) dx`
  (two integrations by parts, the boundary terms vanishing by the Neumann
  data and `sin(kπ) = 0`).
* `summable_norm_cosineCoeff`: `∑ |w_k| < ∞`, i.e. `{w_k} ∈ ℓ¹(ℕ₀)`.
* `hasSum_cosineCoeff`: `w(x) = ∑_{k ≥ 0} w_k cos(k π x / L)` for every
  `x ∈ [0, L]`, via the even `2L`-periodic extension of `w` and Mathlib's
  pointwise convergence of absolutely summable Fourier series on `AddCircle`.
* `cos_cos_cos_of_neumann`, `cos_cos_cos_cos_of_neumann`,
  `cosine_sine_sine_of_neumann`, `two_cosines_two_sines_of_neumann`:
  the identities of `NeumannCosine.ProductIdentities` with the series replaced
  by the functions themselves and the sequences by their cosine coefficients.
-/

set_option autoImplicit false

namespace NeumannCosine.Coefficients

open MeasureTheory Set Real
open scoped Interval

noncomputable section

/-- Classical form of `w ∈ W^{2,1}(0,L)` with Neumann data `w_x(0) = w_x(L) = 0`;
see the module docstring. -/
structure NeumannW21 (L : ℝ) (w w' : ℝ → ℝ) : Prop where
  /-- `w` is absolutely continuous on `[0, L]`. -/
  ac : AbsolutelyContinuousOnInterval w 0 L
  /-- `w' x` is the derivative of `w` at each interior point. -/
  hasDerivAt : ∀ x ∈ Ioo 0 L, HasDerivAt w (w' x) x
  /-- `w'` is absolutely continuous on `[0, L]` (so `w'' ∈ L¹`). -/
  ac_deriv : AbsolutelyContinuousOnInterval w' 0 L
  /-- Neumann condition at `0`. -/
  neumann_left : w' 0 = 0
  /-- Neumann condition at `L`. -/
  neumann_right : w' L = 0

/-- A `C²` function with `w'(0) = w'(L) = 0` lies in the Neumann
class (with `w' = deriv w`). -/
theorem NeumannW21.of_contDiff {L : ℝ} {w : ℝ → ℝ} (hw : ContDiff ℝ 2 w)
    (h0 : deriv w 0 = 0) (hL : deriv w L = 0) : NeumannW21 L w (deriv w) where
  ac := (hw.of_le (by norm_num)).contDiffOn.absolutelyContinuousOnInterval
  hasDerivAt x _ := ((hw.differentiable (by norm_num)) x).hasDerivAt
  ac_deriv := by
    have h1 : ContDiff ℝ 1 (deriv w) := (contDiff_succ_iff_deriv.mp hw).2.2
    exact h1.contDiffOn.absolutelyContinuousOnInterval
  neumann_left := h0
  neumann_right := hL

/-- The Neumann cosine coefficients:
`w_0 = (1/L) ∫₀ᴸ w`, `w_k = (2/L) ∫₀ᴸ w(x) cos(k π x / L) dx` for `k ≥ 1`. -/
def cosineCoeff (L : ℝ) (w : ℝ → ℝ) (k : ℕ) : ℝ :=
  (if k = 0 then 1 / L else 2 / L) *
    ∫ x in (0 : ℝ)..L, w x * Real.cos ((k : ℝ) * Real.pi * x / L)

/-- The zero mode is the mean: `w_0 = (1/L) ∫₀ᴸ w`. -/
theorem cosineCoeff_zero (L : ℝ) (w : ℝ → ℝ) :
    cosineCoeff L w 0 = 1 / L * ∫ x in (0 : ℝ)..L, w x := by
  simp [cosineCoeff]

/-- For `k ≥ 1`, `w_k = (2/L) ∫₀ᴸ w(x) cos(k π x / L) dx`. -/
theorem cosineCoeff_of_ne_zero (L : ℝ) (w : ℝ → ℝ) {k : ℕ} (hk : k ≠ 0) :
    cosineCoeff L w k =
      2 / L * ∫ x in (0 : ℝ)..L, w x * Real.cos ((k : ℝ) * Real.pi * x / L) := by
  simp [cosineCoeff, hk]

/-! ### Two integrations by parts -/

private theorem hasDerivAt_sin_div (ω x : ℝ) (hω : ω ≠ 0) :
    HasDerivAt (fun y => Real.sin (ω * y) / ω) (Real.cos (ω * x)) x := by
  have h1 : HasDerivAt (fun y => ω * y) ω x := by
    simpa using (hasDerivAt_id x).const_mul ω
  have h := h1.sin.div_const ω
  convert h using 1
  field_simp

private theorem hasDerivAt_neg_cos_div (ω x : ℝ) (hω : ω ≠ 0) :
    HasDerivAt (fun y => -Real.cos (ω * y) / ω ^ 2) (Real.sin (ω * x) / ω) x := by
  have h1 : HasDerivAt (fun y => ω * y) ω x := by
    simpa using (hasDerivAt_id x).const_mul ω
  have h3 : HasDerivAt (fun y => -Real.cos (ω * y)) (Real.sin (ω * x) * ω) x := by
    simpa using h1.cos.fun_neg
  have h := h3.div_const (ω ^ 2)
  convert h using 1
  field_simp

/-- Two integrations by parts against `cos (ω x)` with `sin (ω L) = 0`:
`∫₀ᴸ w cos(ωx) = -(1/ω²) ∫₀ᴸ w'' cos(ωx)`, using the Neumann data. -/
theorem integral_mul_cos_eq (L ω : ℝ) (hL : 0 ≤ L) (hω : ω ≠ 0)
    (hωL : Real.sin (ω * L) = 0) {w w' : ℝ → ℝ} (h : NeumannW21 L w w') :
    ∫ x in (0 : ℝ)..L, w x * Real.cos (ω * x) =
      -(1 / ω ^ 2) * ∫ x in (0 : ℝ)..L, deriv w' x * Real.cos (ω * x) := by
  set S : ℝ → ℝ := fun y => Real.sin (ω * y) / ω with hS
  set C : ℝ → ℝ := fun y => -Real.cos (ω * y) / ω ^ 2 with hC
  have hdS : ∀ x, deriv S x = Real.cos (ω * x) := fun x =>
    (hasDerivAt_sin_div ω x hω).deriv
  have hdC : ∀ x, deriv C x = S x := fun x =>
    (hasDerivAt_neg_cos_div ω x hω).deriv
  have hSac : AbsolutelyContinuousOnInterval S 0 L :=
    ContDiffOn.absolutelyContinuousOnInterval (by rw [hS]; fun_prop)
  have hCac : AbsolutelyContinuousOnInterval C 0 L :=
    ContDiffOn.absolutelyContinuousOnInterval (by rw [hC]; fun_prop)
  have step1 := h.ac.integral_mul_deriv_eq_deriv_mul hSac
  have step2 := h.ac_deriv.integral_mul_deriv_eq_deriv_mul hCac
  simp only [hdS, hdC] at step1 step2
  have hcongr : ∫ x in (0 : ℝ)..L, deriv w x * S x =
      ∫ x in (0 : ℝ)..L, w' x * S x :=
    intervalIntegral.integral_congr_Ioo_of_le hL fun x hx => by
      simp only [(h.hasDerivAt x hx).deriv]
  have hS0 : S 0 = 0 := by simp [hS]
  have hSL : S L = 0 := by simp [hS, hωL]
  rw [step1, hcongr, step2, hS0, hSL, h.neumann_left, h.neumann_right]
  have hint : ∫ x in (0 : ℝ)..L, deriv w' x * C x =
      -(1 / ω ^ 2) * ∫ x in (0 : ℝ)..L, deriv w' x * Real.cos (ω * x) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    ext x
    simp only [hC]
    ring
  rw [hint]
  ring

/-- For `k ≥ 1` the cosine coefficient of `w` is `-(L/(kπ))²` times the
corresponding coefficient of `w''`. -/
theorem cosineCoeff_eq_neg_mul_secondDeriv (L : ℝ) (hL : 0 < L) {w w' : ℝ → ℝ}
    (h : NeumannW21 L w w') {k : ℕ} (hk : k ≠ 0) :
    cosineCoeff L w k =
      -(L / ((k : ℝ) * Real.pi)) ^ 2 *
        (2 / L * ∫ x in (0 : ℝ)..L,
          deriv w' x * Real.cos ((k : ℝ) * Real.pi * x / L)) := by
  set ω : ℝ := (k : ℝ) * Real.pi / L with hωdef
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hω : ω ≠ 0 := by positivity
  have hωL : Real.sin (ω * L) = 0 := by
    rw [hωdef, div_mul_cancel₀ _ hL.ne']
    exact Real.sin_nat_mul_pi k
  have harg : ∀ x : ℝ, (k : ℝ) * Real.pi * x / L = ω * x := fun x => by
    rw [hωdef]; ring
  have key := integral_mul_cos_eq L ω hL.le hω hωL h
  rw [cosineCoeff_of_ne_zero L w hk]
  simp only [harg]
  rw [key]
  have : 1 / ω ^ 2 = (L / ((k : ℝ) * Real.pi)) ^ 2 := by
    rw [hωdef]; field_simp
  rw [this]
  ring

/-! ### Absolute summability -/

/-- `|w_k| ≤ (2L/π²) (∫₀ᴸ |w''|) / k²` for `k ≥ 1`. -/
theorem abs_cosineCoeff_le (L : ℝ) (hL : 0 < L) {w w' : ℝ → ℝ}
    (h : NeumannW21 L w w') {k : ℕ} (hk : k ≠ 0) :
    |cosineCoeff L w k| ≤
      2 * L / Real.pi ^ 2 * (∫ x in (0 : ℝ)..L, |deriv w' x|) *
        (1 / (k : ℝ) ^ 2) := by
  rw [cosineCoeff_eq_neg_mul_secondDeriv L hL h hk]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hbound : |∫ x in (0 : ℝ)..L,
      deriv w' x * Real.cos ((k : ℝ) * Real.pi * x / L)| ≤
        ∫ x in (0 : ℝ)..L, |deriv w' x| := by
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le hL.le
      (Filter.Eventually.of_forall fun x _ => ?_) h.ac_deriv.intervalIntegrable_deriv.abs
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (by
      simpa [Real.norm_eq_abs] using Real.abs_cos_le_one _)
  rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 / L)]
  have hsq : |(L / ((k : ℝ) * Real.pi)) ^ 2| =
      L ^ 2 / Real.pi ^ 2 * (1 / (k : ℝ) ^ 2) := by
    rw [abs_of_nonneg (by positivity)]
    field_simp
  rw [hsq]
  calc L ^ 2 / Real.pi ^ 2 * (1 / (k : ℝ) ^ 2) *
        (2 / L * |∫ x in (0 : ℝ)..L,
          deriv w' x * Real.cos ((k : ℝ) * Real.pi * x / L)|)
      ≤ L ^ 2 / Real.pi ^ 2 * (1 / (k : ℝ) ^ 2) *
        (2 / L * ∫ x in (0 : ℝ)..L, |deriv w' x|) := by
        gcongr
    _ = 2 * L / Real.pi ^ 2 * (∫ x in (0 : ℝ)..L, |deriv w' x|) *
        (1 / (k : ℝ) ^ 2) := by
        field_simp

/-- The Neumann cosine coefficients of `w` are absolutely summable:
`{w_k} ∈ ℓ¹(ℕ₀)`. -/
theorem summable_norm_cosineCoeff (L : ℝ) (hL : 0 < L) {w w' : ℝ → ℝ}
    (h : NeumannW21 L w w') : Summable fun k => ‖cosineCoeff L w k‖ := by
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
    (((summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr one_lt_two)).mul_left
      (2 * L / Real.pi ^ 2 * (∫ x in (0 : ℝ)..L, |deriv w' x|)))
  rw [Real.norm_eq_abs]
  exact_mod_cast abs_cosineCoeff_le L hL h (Nat.succ_ne_zero k)

/-! ### Pointwise expansion via the even `2L`-periodic extension -/

/-- The even extension `x ↦ w |x|`, complexified. -/
def evenExt (w : ℝ → ℝ) (x : ℝ) : ℂ :=
  (w |x| : ℂ)

/-- The half-normalized coefficient `(1/L) ∫₀ᴸ w(x) cos(n π x / L) dx`, `n ∈ ℤ`;
it is the `n`-th complex Fourier coefficient of the even `2L`-periodic
extension of `w`. -/
def halfCoeff (L : ℝ) (w : ℝ → ℝ) (n : ℤ) : ℝ :=
  1 / L * ∫ x in (0 : ℝ)..L, w x * Real.cos ((n : ℝ) * Real.pi * x / L)

/-- Evenness of the half-normalized coefficient in the integer index. -/
theorem halfCoeff_neg (L : ℝ) (w : ℝ → ℝ) (n : ℤ) :
    halfCoeff L w (-n) = halfCoeff L w n := by
  unfold halfCoeff
  congr 2
  ext x
  rw [Int.cast_neg, neg_mul, neg_mul, neg_div, Real.cos_neg]

/-- `w_0 = ŵ_0` and `w_k = 2 ŵ_k` for `k ≥ 1`. -/
theorem cosineCoeff_eq_halfCoeff (L : ℝ) (w : ℝ → ℝ) (k : ℕ) :
    cosineCoeff L w k = (if k = 0 then 1 else 2) * halfCoeff L w k := by
  unfold cosineCoeff halfCoeff
  split_ifs <;> simp only [Int.cast_natCast] <;> ring

private theorem continuousOn_w {L : ℝ} (hL : 0 < L) {w w' : ℝ → ℝ}
    (h : NeumannW21 L w w') : ContinuousOn w (Icc 0 L) := by
  simpa [uIcc_of_le hL.le] using h.ac.continuousOn

private theorem continuousOn_evenExt {L : ℝ} (hL : 0 < L) {w w' : ℝ → ℝ}
    (h : NeumannW21 L w w') : ContinuousOn (evenExt w) (Icc (-L) L) := by
  have hmaps : MapsTo (fun x : ℝ => |x|) (Icc (-L) L) (Icc 0 L) := fun x hx =>
    ⟨abs_nonneg x, abs_le.mpr hx⟩
  exact Complex.continuous_ofReal.comp_continuousOn
    ((continuousOn_w hL h).comp continuous_abs.continuousOn hmaps)

/-- The even `2L`-periodic extension of `w`, as a continuous function on the
circle `ℝ / 2Lℤ`. -/
def evenPeriodic {L : ℝ} (hL : 0 < L) {w w' : ℝ → ℝ} (h : NeumannW21 L w w') :
    haveI : Fact (0 < 2 * L) := ⟨by positivity⟩
    C(AddCircle (2 * L), ℂ) :=
  haveI : Fact (0 < 2 * L) := ⟨by positivity⟩
  ⟨AddCircle.liftIco (2 * L) (-L) (evenExt w),
    AddCircle.liftIco_continuous
      (by simp only [evenExt, show -L + 2 * L = L by ring, abs_neg])
      (by rw [show -L + 2 * L = L by ring]; exact continuousOn_evenExt hL h)⟩

private theorem exp_add_exp_neg (L : ℝ) (hL : 0 < L) (n : ℤ) (x : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * (-n : ℤ) * x / (2 * L : ℝ)) +
        Complex.exp (2 * Real.pi * Complex.I * (-n : ℤ) * (-x : ℝ) / (2 * L : ℝ)) =
      ((2 * Real.cos ((n : ℝ) * Real.pi * x / L) : ℝ) : ℂ) := by
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  push_cast
  rw [Complex.two_cos, add_comm]
  congr 1 <;> congr 1 <;> field_simp

/-- The `n`-th Fourier coefficient on `ℝ / 2Lℤ` of the even extension is
`(1/L) ∫₀ᴸ w(x) cos(n π x / L) dx`. -/
theorem fourierCoeff_evenPeriodic {L : ℝ} (hL : 0 < L) {w w' : ℝ → ℝ}
    (h : NeumannW21 L w w') (n : ℤ) :
    haveI : Fact (0 < 2 * L) := ⟨by positivity⟩
    fourierCoeff (evenPeriodic hL h) n = (halfCoeff L w n : ℂ) := by
  have : Fact (0 < 2 * L) := ⟨by positivity⟩
  set g : ℝ → ℂ := fun x =>
    Complex.exp (2 * Real.pi * Complex.I * (-n : ℤ) * x / (2 * L : ℝ)) * evenExt w x
    with hg
  have hgc : ContinuousOn g (Icc (-L) L) := by
    refine ContinuousOn.mul (Continuous.continuousOn (by fun_prop)) ?_
    exact continuousOn_evenExt hL h
  rw [fourierCoeff_eq_intervalIntegral _ n (-L), show -L + 2 * L = L by ring]
  have h1 : ∫ x in (-L)..L, fourier (-n) (x : AddCircle (2 * L)) •
      evenPeriodic hL h (x : AddCircle (2 * L)) = ∫ x in (-L)..L, g x := by
    refine intervalIntegral.integral_congr_Ioo_of_le (by linarith) fun x hx => ?_
    have hx' : x ∈ Ico (-L) (-L + 2 * L) := by
      rw [show -L + 2 * L = L by ring]; exact Ioo_subset_Ico_self hx
    simp only [evenPeriodic, ContinuousMap.coe_mk, AddCircle.liftIco_coe_apply hx',
      fourier_coe_apply, smul_eq_mul, hg]
  rw [h1]
  have hint : ∀ a b : ℝ, a ∈ Icc (-L) L → b ∈ Icc (-L) L →
      IntervalIntegrable g volume a b := fun a b ha hb =>
    (hgc.mono (uIcc_subset_Icc ha hb)).intervalIntegrable
  have hm : (-L : ℝ) ∈ Icc (-L) L := ⟨le_rfl, by linarith⟩
  have hz : (0 : ℝ) ∈ Icc (-L) L := ⟨by linarith, hL.le⟩
  have hp : (L : ℝ) ∈ Icc (-L) L := ⟨by linarith, le_rfl⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint _ _ hm hz) (hint _ _ hz hp)]
  have hneg : ∫ x in (-L)..0, g x = ∫ x in (0 : ℝ)..L, g (-x) := by
    rw [intervalIntegral.integral_comp_neg, neg_zero]
  have hnegint : IntervalIntegrable (fun x => g (-x)) volume 0 L := by
    have hc : ContinuousOn (fun x => g (-x)) (Icc 0 L) :=
      hgc.comp continuous_neg.continuousOn fun y hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩
    exact (hc.mono (by rw [uIcc_of_le hL.le])).intervalIntegrable
  rw [hneg, ← intervalIntegral.integral_add hnegint (hint _ _ hz hp)]
  have h2 : ∫ x in (0 : ℝ)..L, g (-x) + g x =
      ∫ x in (0 : ℝ)..L,
        ((2 * (w x * Real.cos ((n : ℝ) * Real.pi * x / L)) : ℝ) : ℂ) := by
    refine intervalIntegral.integral_congr_Ioo_of_le hL.le fun x hx => ?_
    have hax : |x| = x := abs_of_pos hx.1
    have := exp_add_exp_neg L hL n x
    simp only [hg, evenExt, abs_neg, hax]
    rw [← add_mul, add_comm, this]
    push_cast
    ring
  rw [h2, intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul]
  unfold halfCoeff
  rw [Complex.real_smul]
  push_cast
  field_simp

/-- `w x` for `x ∈ [0, L]` is the value of the even periodic extension. -/
theorem evenPeriodic_apply {L : ℝ} (hL : 0 < L) {w w' : ℝ → ℝ}
    (h : NeumannW21 L w w') {x : ℝ} (hx : x ∈ Icc 0 L) :
    haveI : Fact (0 < 2 * L) := ⟨by positivity⟩
    evenPeriodic hL h (x : AddCircle (2 * L)) = (w x : ℂ) := by
  have : Fact (0 < 2 * L) := ⟨by positivity⟩
  rcases eq_or_lt_of_le hx.2 with hxL | hxL
  · have hcoe : ((x : ℝ) : AddCircle (2 * L)) = ((-L : ℝ) : AddCircle (2 * L)) := by
      rw [← AddCircle.coe_add_period (2 * L) (-L), hxL]
      congr 1
      ring
    have hmem : (-L : ℝ) ∈ Ico (-L) (-L + 2 * L) := ⟨le_rfl, by linarith⟩
    rw [hcoe]
    simp only [evenPeriodic, ContinuousMap.coe_mk, AddCircle.liftIco_coe_apply hmem,
      evenExt, abs_neg, abs_of_pos hL, hxL]
  · have hmem : x ∈ Ico (-L) (-L + 2 * L) := ⟨by linarith [hx.1], by linarith⟩
    simp only [evenPeriodic, ContinuousMap.coe_mk, AddCircle.liftIco_coe_apply hmem,
      evenExt, abs_of_nonneg hx.1]

/-- The half-normalized coefficients are summable over `ℤ`. -/
theorem summable_halfCoeff (L : ℝ) (hL : 0 < L) {w w' : ℝ → ℝ}
    (h : NeumannW21 L w w') : Summable fun n : ℤ => halfCoeff L w n := by
  have hnat : Summable fun k : ℕ => halfCoeff L w k := by
    refine Summable.of_norm_bounded (summable_norm_cosineCoeff L hL h) fun k => ?_
    rw [cosineCoeff_eq_halfCoeff, norm_mul]
    split_ifs
    · norm_num
    · norm_num
      linarith [abs_nonneg (halfCoeff L w k)]
  refine Summable.of_nat_of_neg hnat ?_
  simpa only [halfCoeff_neg] using hnat

/-- **Cosine expansion.**  For `w` in the Neumann class and `x ∈ [0, L]`,
`w(x) = ∑_{k ≥ 0} w_k cos(k π x / L)`, and the series converges absolutely. -/
theorem hasSum_cosineCoeff (L : ℝ) (hL : 0 < L) {w w' : ℝ → ℝ}
    (h : NeumannW21 L w w') {x : ℝ} (hx : x ∈ Icc 0 L) :
    HasSum (fun k : ℕ => cosineCoeff L w k * Real.cos ((k : ℝ) * Real.pi * x / L))
      (w x) := by
  have : Fact (0 < 2 * L) := ⟨by positivity⟩
  have hsum : Summable (fourierCoeff (evenPeriodic hL h)) := by
    have : fourierCoeff (evenPeriodic hL h) = fun n => (halfCoeff L w n : ℂ) :=
      funext (fourierCoeff_evenPeriodic hL h)
    rw [this]
    exact Complex.summable_ofReal.mpr (summable_halfCoeff L hL h)
  have hp := has_pointwise_sum_fourier_series_of_summable hsum (x : AddCircle (2 * L))
  rw [evenPeriodic_apply hL h hx] at hp
  have hq := hp.nat_add_neg
  simp only [fourierCoeff_evenPeriodic hL h, fourier_coe_apply, halfCoeff_neg,
    smul_eq_mul, Int.cast_zero, mul_zero, zero_mul, zero_div, Complex.exp_zero,
    mul_one] at hq
  have hterm : ∀ k : ℕ,
      (halfCoeff L w k : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((k : ℤ) : ℂ) * x / (2 * L : ℝ)) +
        (halfCoeff L w k : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((-(k : ℤ) : ℤ) : ℂ) * x / (2 * L : ℝ)) =
      ((2 * halfCoeff L w k * Real.cos ((k : ℝ) * Real.pi * x / L) : ℝ) : ℂ) := by
    intro k
    have := exp_add_exp_neg L hL (k : ℤ) (-x)
    rw [← mul_add]
    have e1 : Complex.exp (2 * Real.pi * Complex.I * ((k : ℤ) : ℂ) * x / (2 * L : ℝ)) =
        Complex.exp (2 * Real.pi * Complex.I * ((-(k : ℤ) : ℤ) : ℂ) * ((-x : ℝ) : ℂ) /
          (2 * L : ℝ)) := by
      congr 1; push_cast; ring
    have e2 : Complex.exp (2 * Real.pi * Complex.I * ((-(k : ℤ) : ℤ) : ℂ) * x /
          (2 * L : ℝ)) =
        Complex.exp (2 * Real.pi * Complex.I * ((-(k : ℤ) : ℤ) : ℂ) * ((-(-x) : ℝ) : ℂ) /
          (2 * L : ℝ)) := by
      congr 1; push_cast; ring
    rw [e1, e2, this]
    push_cast
    rw [show (k : ℂ) * (Real.pi : ℂ) * -(x : ℂ) / (L : ℂ) =
      -((k : ℂ) * (Real.pi : ℂ) * (x : ℂ) / (L : ℂ)) by ring, Complex.cos_neg]
    ring
  have hq2 : HasSum
      (fun k : ℕ => ((2 * halfCoeff L w k * Real.cos ((k : ℝ) * Real.pi * x / L) : ℝ) : ℂ))
      ((w x + halfCoeff L w 0 : ℝ) : ℂ) := by
    convert hq using 1
    · funext k
      exact (hterm k).symm
    · push_cast
      ring
  have hr := (Complex.hasSum_ofReal.mp hq2).sub (hasSum_ite_eq 0 (halfCoeff L w 0))
  convert hr using 1
  · funext k
    rw [cosineCoeff_eq_halfCoeff]
    split_ifs with hk
    · subst hk
      simp only [CharP.cast_eq_zero, zero_mul, zero_div, Real.cos_zero]
      ring
    · ring
  · ring

/-! ### Product identities for functions with Neumann data -/

/-- On `[0, L]` the function equals its cosine series. -/
theorem tsum_cosineCoeff_eq (L : ℝ) (hL : 0 < L) {w w' : ℝ → ℝ}
    (h : NeumannW21 L w w') {x : ℝ} (hx : x ∈ Icc 0 L) :
    ∑' k : ℕ, cosineCoeff L w k * Real.cos ((k : ℝ) * Real.pi * x / L) = w x :=
  (hasSum_cosineCoeff L hL h hx).tsum_eq

private theorem mem_Icc_of_mem_uIcc {L x : ℝ} (hL : 0 < L) (hx : x ∈ [[(0 : ℝ), L]]) :
    x ∈ Icc 0 L := by
  rwa [uIcc_of_le hL.le] at hx

/-- `ProductIdentities.cosine_sine_sine` for `u` in the Neumann class, with its
cosine coefficients `u_i`. -/
theorem cosine_sine_sine_of_neumann (L : ℝ) (hL : 0 < L) {u u' : ℝ → ℝ}
    (hu : NeumannW21 L u u') (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∫ x in (0 : ℝ)..L,
        u x * Real.sin ((n : ℝ) * Real.pi * x / L) *
          Real.sin ((k : ℝ) * Real.pi * x / L) =
      L / 4 * (cosineCoeff L u (Int.natAbs ((n : ℤ) - k)) - cosineCoeff L u (n + k) +
        (if n = k then cosineCoeff L u 0 else 0)) := by
  rw [← ProductIdentities.cosine_sine_sine L hL (cosineCoeff L u)
    (summable_norm_cosineCoeff L hL hu) n k hn hk]
  refine intervalIntegral.integral_congr fun x hx => ?_
  simp only [tsum_cosineCoeff_eq L hL hu (mem_Icc_of_mem_uIcc hL hx)]

/-- `ProductIdentities.two_cosines_two_sines` for `u, v` in the Neumann class,
with their cosine coefficients. -/
theorem two_cosines_two_sines_of_neumann (L : ℝ) (hL : 0 < L) {u u' v v' : ℝ → ℝ}
    (hu : NeumannW21 L u u') (hv : NeumannW21 L v v') (n k : ℕ)
    (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∫ x in (0 : ℝ)..L,
        u x * v x * Real.sin ((n : ℝ) * Real.pi * x / L) *
          Real.sin ((k : ℝ) * Real.pi * x / L) =
      L / 8 *
        ((∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = (n : ℤ) - k},
            cosineCoeff L u p.1.1 * cosineCoeff L v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = -((n : ℤ) - k)},
            cosineCoeff L u p.1.1 * cosineCoeff L v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) + p.2 = (n : ℤ) - k},
            cosineCoeff L u p.1.1 * cosineCoeff L v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) + p.2 = -((n : ℤ) - k)},
            cosineCoeff L u p.1.1 * cosineCoeff L v p.1.2) -
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = (n : ℤ) + k},
            cosineCoeff L u p.1.1 * cosineCoeff L v p.1.2) -
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = -((n : ℤ) + k)},
            cosineCoeff L u p.1.1 * cosineCoeff L v p.1.2) -
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) + p.2 = (n : ℤ) + k},
            cosineCoeff L u p.1.1 * cosineCoeff L v p.1.2)) := by
  rw [← ProductIdentities.two_cosines_two_sines L hL (cosineCoeff L u) (cosineCoeff L v)
    (summable_norm_cosineCoeff L hL hu) (summable_norm_cosineCoeff L hL hv) n k hn hk]
  refine intervalIntegral.integral_congr fun x hx => ?_
  simp only [tsum_cosineCoeff_eq L hL hu (mem_Icc_of_mem_uIcc hL hx),
    tsum_cosineCoeff_eq L hL hv (mem_Icc_of_mem_uIcc hL hx)]

/-- `ProductIdentities.cos_cos_cos` (`k ≥ 0`) for `u, v` in the Neumann class,
with their cosine coefficients. -/
theorem cos_cos_cos_of_neumann (L : ℝ) (hL : 0 < L) {u u' v v' : ℝ → ℝ}
    (hu : NeumannW21 L u u') (hv : NeumannW21 L v v') (k : ℕ) :
    ∫ x in (0 : ℝ)..L, u x * v x * Real.cos ((k : ℝ) * Real.pi * x / L) =
      L / 4 * ((∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = k},
            cosineCoeff L u p.1.1 * cosineCoeff L v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = -(k : ℤ)},
            cosineCoeff L u p.1.1 * cosineCoeff L v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) + p.2 = k},
            cosineCoeff L u p.1.1 * cosineCoeff L v p.1.2)) +
        L / 4 * (if k = 0 then cosineCoeff L u 0 * cosineCoeff L v 0 else 0) := by
  rw [← ProductIdentities.cos_cos_cos L hL (cosineCoeff L u) (cosineCoeff L v)
    (summable_norm_cosineCoeff L hL hu) (summable_norm_cosineCoeff L hL hv) k]
  refine intervalIntegral.integral_congr fun x hx => ?_
  simp only [tsum_cosineCoeff_eq L hL hu (mem_Icc_of_mem_uIcc hL hx),
    tsum_cosineCoeff_eq L hL hv (mem_Icc_of_mem_uIcc hL hx)]

/-- `ProductIdentities.cos_cos_cos_cos` (`k ≥ 0`) for `u, v, w` in the Neumann
class, with their cosine coefficients. -/
theorem cos_cos_cos_cos_of_neumann (L : ℝ) (hL : 0 < L) {u u' v v' w w' : ℝ → ℝ}
    (hu : NeumannW21 L u u') (hv : NeumannW21 L v v') (hw : NeumannW21 L w w')
    (k : ℕ) :
    ∫ x in (0 : ℝ)..L, u x * v x * w x * Real.cos ((k : ℝ) * Real.pi * x / L) =
      L / 8 *
        ((∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) + t.2.1 + t.2.2 = k},
            cosineCoeff L u t.1.1 * cosineCoeff L v t.1.2.1 * cosineCoeff L w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) + t.2.1 - t.2.2 = k},
            cosineCoeff L u t.1.1 * cosineCoeff L v t.1.2.1 * cosineCoeff L w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) + t.2.1 - t.2.2 = -(k : ℤ)},
            cosineCoeff L u t.1.1 * cosineCoeff L v t.1.2.1 * cosineCoeff L w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 + t.2.2 = k},
            cosineCoeff L u t.1.1 * cosineCoeff L v t.1.2.1 * cosineCoeff L w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 + t.2.2 = -(k : ℤ)},
            cosineCoeff L u t.1.1 * cosineCoeff L v t.1.2.1 * cosineCoeff L w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 - t.2.2 = k},
            cosineCoeff L u t.1.1 * cosineCoeff L v t.1.2.1 * cosineCoeff L w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 - t.2.2 = -(k : ℤ)},
            cosineCoeff L u t.1.1 * cosineCoeff L v t.1.2.1 * cosineCoeff L w t.1.2.2)) +
        L / 8 * (if k = 0 then
          cosineCoeff L u 0 * cosineCoeff L v 0 * cosineCoeff L w 0 else 0) := by
  rw [← ProductIdentities.cos_cos_cos_cos L hL (cosineCoeff L u) (cosineCoeff L v)
    (cosineCoeff L w) (summable_norm_cosineCoeff L hL hu)
    (summable_norm_cosineCoeff L hL hv) (summable_norm_cosineCoeff L hL hw) k]
  refine intervalIntegral.integral_congr fun x hx => ?_
  simp only [tsum_cosineCoeff_eq L hL hu (mem_Icc_of_mem_uIcc hL hx),
    tsum_cosineCoeff_eq L hL hv (mem_Icc_of_mem_uIcc hL hx),
    tsum_cosineCoeff_eq L hL hw (mem_Icc_of_mem_uIcc hL hx)]

end

end NeumannCosine.Coefficients
