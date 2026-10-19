module
/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
Portions adapted from chenle02/Chemataxis_Numerics (MIT).
-/

public import Mathlib

@[expose] public section

/-!
# Neumann cosine modes on `[0, L]`

The Neumann mode of index `k` on `[0, L]` is `cos (k π x / L)`.
Its frequency is `k π / L`.

## Main definitions

* `freq L k`: the frequency `k π / L`.
* `mode L k x`: the mode `cos (k π x / L)`.

## Main results

* `integral_mode_mul_mode`: the Gram values
  `∫₀ᴸ cos_m cos_n = L` if `m = n = 0`, `L / 2` if `m = n ≠ 0`, and `0` if `m ≠ n`.
* `normalized_integral_mode_mul_self`: `(2/L) ∫₀ᴸ cos_n cos_n = 1` for `n ≥ 1`.
* `normalized_integral_mode_three_mul`: `(2/L) ∫₀ᴸ cos_{3n} cos_n = 0` for `n ≥ 1`.
* `normalized_integral_mode_pow_four`: `(2/L) ∫₀ᴸ cos_n⁴ = 3/4` for `n ≥ 1`.

Some files state results with the raw expression `Real.cos (k * π * x / L)`.
The lemmas `mode_eq_cos_freq` and `cos_freq_mul` relate the spellings.
-/

namespace NeumannCosine

open Real

noncomputable section

/-! ### The frequency and the mode -/

/-- The frequency `k π / L` of the `k`-th Neumann mode on `[0, L]`. -/
def freq (L : ℝ) (k : ℕ) : ℝ := k * π / L

theorem freq_nonneg {L : ℝ} (hL : 0 < L) (k : ℕ) : 0 ≤ freq L k := by
  unfold freq; positivity

theorem freq_mul_length {L : ℝ} (hL : 0 < L) (k : ℕ) : freq L k * L = k * π := by
  unfold freq; field_simp

/-- The cosine with frequency `freq L k` is `cos (k π x / L)`. -/
theorem cos_freq_mul (L : ℝ) (k : ℕ) (x : ℝ) : cos (freq L k * x) = cos (k * π * x / L) := by
  unfold freq; ring_nf

/-- The Neumann mode `cos (k π x / L)` on `[0, L]`. -/
def mode (L : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  Real.cos ((k : ℝ) * Real.pi * x / L)

theorem mode_eq_cos_freq (L : ℝ) (k : ℕ) (x : ℝ) : mode L k x = cos (freq L k * x) :=
  (cos_freq_mul L k x).symm

theorem continuous_mode (L : ℝ) (n : ℕ) :
    Continuous (mode L n) := by
  unfold mode
  fun_prop

theorem norm_mode_le_one (L : ℝ) (n : ℕ) (x : ℝ) :
    ‖mode L n x‖ ≤ 1 := by
  simpa only [mode, Real.norm_eq_abs] using
    Real.abs_cos_le_one ((n : ℝ) * Real.pi * x / L)

/-! ### A product-to-sum identity -/

theorem cos_pow_three (theta : ℝ) :
    Real.cos theta ^ 3 =
      (3 * Real.cos theta + Real.cos (3 * theta)) / 4 := by
  rw [Real.cos_three_mul]
  ring_nf

/-! ### Orthogonality -/

lemma integral_cos_const_mul (c L : ℝ) (hc : c ≠ 0) :
    (∫ y in (0 : ℝ)..L, Real.cos (c * y)) = Real.sin (c * L) / c := by
  rw [intervalIntegral.integral_comp_mul_left (fun y => Real.cos y) hc,
    integral_cos]
  simp
  ring

/-- `∫₀ᴸ cos (j π y / L) dy` is `L` if `j = 0` and `0` otherwise, for `j ∈ ℤ`. -/
lemma integral_cos_int_mul_pi_div (L : ℝ) (hL : 0 < L) (j : ℤ) :
    (∫ y in (0 : ℝ)..L,
      Real.cos (((j : ℝ) * Real.pi / L) * y)) =
        if j = 0 then L else 0 := by
  by_cases hj : j = 0
  · subst hj
    simp
  · rw [if_neg hj]
    have hj' : (j : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hj
    have hc : (j : ℝ) * Real.pi / L ≠ 0 :=
      div_ne_zero (mul_ne_zero hj' (ne_of_gt Real.pi_pos)) (ne_of_gt hL)
    rw [integral_cos_const_mul _ _ hc]
    have hstep : (j : ℝ) * Real.pi / L * L = (j : ℝ) * Real.pi := by
      field_simp
    rw [hstep, Real.sin_int_mul_pi]
    simp

/-- Orthogonality of the Neumann modes and their Gram values. -/
theorem integral_mode_mul_mode
    (L : ℝ) (hL : 0 < L) (m n : ℕ) :
    (∫ y in (0 : ℝ)..L, mode L m y * mode L n y) =
      if m = n then (if m = 0 then L else L / 2) else 0 := by
  have key : ∀ y : ℝ, mode L m y * mode L n y =
      (Real.cos ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * Real.pi / L * y) +
        Real.cos ((((m : ℤ) + (n : ℤ) : ℤ) : ℝ) * Real.pi / L * y)) / 2 := by
    intro y
    simp only [mode_eq_cos_freq, freq]
    have c1 : ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ)) =
        (m : ℝ) - (n : ℝ) := by push_cast; ring
    have c2 : ((((m : ℤ) + (n : ℤ) : ℤ) : ℝ)) =
        (m : ℝ) + (n : ℝ) := by push_cast; ring
    rw [c1, c2]
    have e1 : ((m : ℝ) - (n : ℝ)) * Real.pi / L * y =
        (m : ℝ) * Real.pi / L * y - (n : ℝ) * Real.pi / L * y := by
      field_simp
    have e2 : ((m : ℝ) + (n : ℝ)) * Real.pi / L * y =
        (m : ℝ) * Real.pi / L * y + (n : ℝ) * Real.pi / L * y := by
      field_simp
    rw [e1, e2, Real.cos_sub, Real.cos_add]
    ring
  have hcont1 : Continuous fun y : ℝ =>
      Real.cos (((((m : ℤ) - (n : ℤ) : ℤ) : ℝ)) * Real.pi / L * y) := by
    continuity
  have hcont2 : Continuous fun y : ℝ =>
      Real.cos (((((m : ℤ) + (n : ℤ) : ℤ) : ℝ)) * Real.pi / L * y) := by
    continuity
  rw [intervalIntegral.integral_congr (g := fun y =>
        (Real.cos (((((m : ℤ) - (n : ℤ) : ℤ) : ℝ)) * Real.pi / L * y) +
          Real.cos (((((m : ℤ) + (n : ℤ) : ℤ) : ℝ)) * Real.pi / L * y)) / 2)
        (fun y _ => key y)]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_add
      (hcont1.intervalIntegrable _ _) (hcont2.intervalIntegrable _ _),
    integral_cos_int_mul_pi_div L hL, integral_cos_int_mul_pi_div L hL]
  by_cases hmn : m = n
  · subst hmn
    by_cases hm : m = 0
    · subst hm
      norm_num
    · have hsum : ((m : ℤ) + (m : ℤ)) ≠ 0 := by
        have hm' : (m : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hm
        omega
      simp [hsum, hm]
  · have hdiff : ((m : ℤ) - (n : ℤ)) ≠ 0 := by
      intro h
      exact hmn (by exact_mod_cast sub_eq_zero.mp h)
    have hsum : ((m : ℤ) + (n : ℤ)) ≠ 0 := by
      rcases Nat.eq_zero_or_pos m with hm | hm
      · rcases Nat.eq_zero_or_pos n with hn | hn
        · exact absurd (hm.trans hn.symm) hmn
        · omega
      · omega
    simp [hdiff, hsum, hmn]

/-! ### Normalized projections -/

/-- For `n ≥ 1`, `(2/L) ∫₀ᴸ cos_n cos_n = 1`. -/
theorem normalized_integral_mode_mul_self
    (L : ℝ) (n : ℕ) (hL : 0 < L) (hn : 0 < n) :
    2 / L * (∫ y in (0 : ℝ)..L,
      mode L n y * mode L n y) = 1 := by
  rw [integral_mode_mul_mode L hL]
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  simp [hn0, ne_of_gt hL]

/-- For `n ≥ 1`, the third harmonic is orthogonal to mode `n`:
`(2/L) ∫₀ᴸ cos_{3n} cos_n = 0`. -/
theorem normalized_integral_mode_three_mul
    (L : ℝ) (n : ℕ) (hL : 0 < L) (hn : 0 < n) :
    2 / L * (∫ y in (0 : ℝ)..L,
      mode L (3 * n) y * mode L n y) = 0 := by
  rw [integral_mode_mul_mode L hL]
  have h3n : 3 * n ≠ n := by omega
  simp [h3n]

/-- For `n ≥ 1`, `(2/L) ∫₀ᴸ cos_n⁴ = 3/4`. -/
theorem normalized_integral_mode_pow_four
    (L : ℝ) (n : ℕ) (hL : 0 < L) (hn : 0 < n) :
    2 / L * (∫ y in (0 : ℝ)..L,
      mode L n y ^ 3 * mode L n y) = 3 / 4 := by
  rw [show (fun y : ℝ => mode L n y ^ 3 * mode L n y) =
      fun y => (3 / 4 : ℝ) *
          (mode L n y * mode L n y) +
        (1 / 4 : ℝ) *
          (mode L (3 * n) y * mode L n y) by
      funext y
      unfold mode
      rw [cos_pow_three]
      push_cast
      ring_nf]
  have hcont : ∀ m : ℕ, Continuous (mode L m) := by
    intro m
    unfold mode
    continuity
  rw [intervalIntegral.integral_add
      (f := fun y => (3 / 4 : ℝ) *
        (mode L n y * mode L n y))
      (g := fun y => (1 / 4 : ℝ) *
        (mode L (3 * n) y * mode L n y))
      ((continuous_const.mul ((hcont n).mul (hcont n))).intervalIntegrable _ _)
      ((continuous_const.mul ((hcont (3 * n)).mul (hcont n))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_mode_mul_mode L hL,
    integral_mode_mul_mode L hL]
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have h3n : 3 * n ≠ n := by omega
  simp [hn0, h3n]
  field_simp [ne_of_gt hL]

end

end NeumannCosine
