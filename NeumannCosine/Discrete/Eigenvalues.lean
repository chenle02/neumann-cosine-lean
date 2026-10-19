/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib

/-!
# Discrete and continuum Neumann eigenvalues on an interval

The Neumann Laplacian on `[0, L]` has eigenvalues `(n * π / L) ^ 2`. The
three-point finite-difference Laplacian on a uniform mesh with `N` intervals
and mesh width `h = L / N` has eigenvalues `4 / h ^ 2 * sin (n * π / (2 * N)) ^ 2`.

This file proves:
* the discrete eigenvalue equals the continuum one times `sinc ^ 2` of the half angle;
* for each fixed mode, the discrete eigenvalue converges to the continuum one;
* among the modes `1 ≤ n ≤ N`, the first mode has the smallest discrete eigenvalue;
* the uniform lower bound `4 * n ^ 2 / L ^ 2` for the discrete eigenvalues;
* positivity and divergence of the continuum eigenvalues, and existence of a
  minimizer for a real sequence tending to `+∞`.
-/

@[expose] public section

set_option autoImplicit false

namespace NeumannCosine.Discrete.Eigenvalues

open Filter
open scoped Topology

/-- The continuum Neumann eigenvalue `(n * π / L) ^ 2`. -/
noncomputable def neumannEigenvalue (L : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * Real.pi / L) ^ 2

/-- The half angle `n * π / (2 * N)` in the discrete eigenvalue. -/
noncomputable def discreteHalfAngle (n N : ℕ) : ℝ :=
  (n : ℝ) * Real.pi / (2 * (N : ℝ))

/-- The discrete Neumann eigenvalue of the three-point Laplacian with mesh
width `h = L / N`. -/
noncomputable def discreteNeumannEigenvalue (L : ℝ) (n N : ℕ) : ℝ :=
  4 / (L / (N : ℝ)) ^ 2 * Real.sin (discreteHalfAngle n N) ^ 2

/-- The discrete eigenvalue is the continuum eigenvalue times `sinc ^ 2` of
the half angle. -/
theorem discreteNeumannEigenvalue_eq_mul_sinc_sq (L : ℝ) (n N : ℕ)
    (hL : L ≠ 0) (hn : 0 < n) (hN : 0 < N) :
    discreteNeumannEigenvalue L n N =
      neumannEigenvalue L n * Real.sinc (discreteHalfAngle n N) ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have harg : discreteHalfAngle n N ≠ 0 := by
    unfold discreteHalfAngle
    exact div_ne_zero (mul_ne_zero hn0 Real.pi_ne_zero) (mul_ne_zero two_ne_zero hN0)
  rw [Real.sinc_of_ne_zero harg]
  unfold discreteNeumannEigenvalue neumannEigenvalue discreteHalfAngle
  field_simp
  ring

/-- For a fixed mode, the half angle tends to zero as the mesh is refined. -/
theorem discreteHalfAngle_tendsto_zero (n : ℕ) :
    Tendsto (discreteHalfAngle n) atTop (𝓝 0) := by
  have h : Tendsto (fun N : ℕ => ((n : ℝ) * Real.pi / 2) / (N : ℝ))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  convert h using 1
  funext N
  unfold discreteHalfAngle
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
  ring

/-- For a fixed mode, the discrete eigenvalue converges to the continuum one. -/
theorem discreteNeumannEigenvalue_tendsto (L : ℝ) (n : ℕ) (hL : 0 < L) (hn : 0 < n) :
    Tendsto (discreteNeumannEigenvalue L n) atTop (𝓝 (neumannEigenvalue L n)) := by
  have harg := discreteHalfAngle_tendsto_zero n
  have hsinc : Tendsto (fun N : ℕ => Real.sinc (discreteHalfAngle n N)) atTop (𝓝 1) := by
    change Tendsto (Real.sinc ∘ discreteHalfAngle n) atTop (𝓝 1)
    simpa only [Real.sinc_zero] using
      Real.continuous_sinc.continuousAt.tendsto.comp harg
  have hnormalized : Tendsto
      (fun N : ℕ => neumannEigenvalue L n * Real.sinc (discreteHalfAngle n N) ^ 2)
      atTop (𝓝 (neumannEigenvalue L n)) := by
    simpa using tendsto_const_nhds.mul (hsinc.pow 2)
  apply hnormalized.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  exact (discreteNeumannEigenvalue_eq_mul_sinc_sq L n N (ne_of_gt hL) hn hN).symm

/-- For a mode `n ≤ N`, the half angle lies in `[0, π / 2]`. -/
theorem discreteHalfAngle_mem_Icc (n N : ℕ) (hN : 0 < N) (hnN : n ≤ N) :
    discreteHalfAngle n N ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hnr : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
  constructor
  · unfold discreteHalfAngle
    positivity
  · unfold discreteHalfAngle
    rw [div_le_iff₀ (by positivity : 0 < 2 * (N : ℝ))]
    nlinarith [Real.pi_pos]

/-- The half angle of the first mode is no larger than that of any positive mode. -/
theorem discreteHalfAngle_one_le (n N : ℕ) (hN : 0 < N) (hn : 1 ≤ n) :
    discreteHalfAngle 1 N ≤ discreteHalfAngle n N := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hnr : ((1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  unfold discreteHalfAngle
  apply div_le_div_of_nonneg_right
  · exact mul_le_mul_of_nonneg_right hnr Real.pi_pos.le
  · positivity

/-- Among the modes `1 ≤ n ≤ N`, the first mode has the smallest discrete
eigenvalue. -/
theorem discreteNeumannEigenvalue_one_le (L : ℝ) (n N : ℕ)
    (hL : 0 < L) (hN : 0 < N) (hn : 1 ≤ n) (hnN : n ≤ N) :
    discreteNeumannEigenvalue L 1 N ≤ discreteNeumannEigenvalue L n N := by
  have harg1 := discreteHalfAngle_mem_Icc 1 N hN (hn.trans hnN)
  have hargn := discreteHalfAngle_mem_Icc n N hN hnN
  have hargle := discreteHalfAngle_one_le n N hN hn
  have hsinle : Real.sin (discreteHalfAngle 1 N) ≤ Real.sin (discreteHalfAngle n N) :=
    Real.strictMonoOn_sin.monotoneOn
      ⟨(neg_nonpos.mpr (by positivity)).trans harg1.1, harg1.2⟩
      ⟨(neg_nonpos.mpr (by positivity)).trans hargn.1, hargn.2⟩ hargle
  have hsin1 : 0 ≤ Real.sin (discreteHalfAngle 1 N) :=
    Real.sin_nonneg_of_nonneg_of_le_pi harg1.1
      (harg1.2.trans (by linarith [Real.pi_pos]))
  have hsquare : Real.sin (discreteHalfAngle 1 N) ^ 2 ≤
      Real.sin (discreteHalfAngle n N) ^ 2 :=
    pow_le_pow_left₀ hsin1 hsinle 2
  unfold discreteNeumannEigenvalue
  exact mul_le_mul_of_nonneg_left hsquare (by positivity)

/-- Concavity of the sine on `[0, π / 2]` gives the uniform quadratic lower
bound `4 * n ^ 2 / L ^ 2` for the discrete eigenvalues. -/
theorem discreteNeumannEigenvalue_lower_bound (L : ℝ) (n N : ℕ)
    (hL : 0 < L) (hN : 0 < N) (hnN : n ≤ N) :
    4 * (n : ℝ) ^ 2 / L ^ 2 ≤ discreteNeumannEigenvalue L n N := by
  have ha := discreteHalfAngle_mem_Icc n N hN hnN
  have hs := Real.mul_le_sin ha.1 ha.2
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hid : 2 / Real.pi * discreteHalfAngle n N = (n : ℝ) / (N : ℝ) := by
    unfold discreteHalfAngle
    field_simp
  rw [hid] at hs
  have hs2 := pow_le_pow_left₀ (by positivity : 0 ≤ (n : ℝ) / (N : ℝ)) hs 2
  have hp := mul_le_mul_of_nonneg_left hs2
    (by positivity : 0 ≤ 4 / (L / (N : ℝ)) ^ 2)
  unfold discreteNeumannEigenvalue
  calc
    4 * (n : ℝ) ^ 2 / L ^ 2 =
        4 / (L / (N : ℝ)) ^ 2 * ((n : ℝ) / (N : ℝ)) ^ 2 := by
      field_simp [hL.ne', hN0] <;> ring
    _ ≤ 4 / (L / (N : ℝ)) ^ 2 * Real.sin (discreteHalfAngle n N) ^ 2 := hp

/-- Every positive-mode continuum Neumann eigenvalue is positive. -/
theorem neumannEigenvalue_pos (L : ℝ) (n : ℕ) (hL : 0 < L) (hn : 0 < n) :
    0 < neumannEigenvalue L n := by
  unfold neumannEigenvalue
  positivity

/-- The continuum Neumann eigenvalues along the positive modes diverge. -/
theorem neumannEigenvalue_succ_tendsto_atTop (L : ℝ) (hL : 0 < L) :
    Tendsto (fun n : ℕ => neumannEigenvalue L (n + 1)) atTop atTop := by
  have hnat : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hscaled : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * Real.pi / L)
      atTop atTop :=
    by
      simpa [mul_comm] using
        (hnat.const_mul_atTop Real.pi_pos).atTop_div_const hL
  simpa [neumannEigenvalue, pow_two] using
    hscaled.atTop_mul_atTop₀ hscaled

/-- A real sequence indexed by the natural numbers and tending to `+∞`
attains a global minimum. -/
theorem exists_forall_le_of_tendsto_atTop (f : ℕ → ℝ)
    (hf : Tendsto f atTop atTop) :
    ∃ n₀, ∀ n, f n₀ ≤ f n := by
  have hev : ∀ᶠ n in atTop, f 0 ≤ f n := hf.eventually_ge_atTop (f 0)
  rw [eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  have hnonempty : (Finset.range (N + 1)).Nonempty := by
    exact ⟨0, by simp⟩
  obtain ⟨n₀, hn₀, hmin⟩ :=
    Finset.exists_min_image (Finset.range (N + 1)) f hnonempty
  refine ⟨n₀, fun n => ?_⟩
  by_cases hn : n < N + 1
  · exact hmin n (Finset.mem_range.mpr hn)
  · have hNn : N ≤ n := by omega
    exact (hmin 0 (by simp)).trans (hN n hNn)

end NeumannCosine.Discrete.Eigenvalues
