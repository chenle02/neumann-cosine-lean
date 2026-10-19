/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import NeumannCosine.Discrete.Eigenvalues

/-!
# Uniform tail cutoffs for modal minima

Let `f : ℝ → ℝ` be continuous at every positive point and satisfy the linear
lower bound `K * x ≤ f x` for `x > 0`, with `K > 0`. Evaluate `f` at the
Neumann eigenvalues. This file shows that a single cutoff `k` works for all
sufficiently fine meshes: every mode `n > k` has a strictly larger value than
the first mode, both for the discrete eigenvalues and for the continuum
eigenvalues. It also records that a finite minimum is unchanged by removing
modes that lie above a retained one.
-/

@[expose] public section

set_option autoImplicit false

namespace NeumannCosine.Discrete.ModalMinimumTail

open Filter
open scoped Topology
open NeumannCosine.Discrete.Eigenvalues

/-- A positive quadratic sequence eventually exceeds any prescribed bound. -/
theorem exists_quadratic_tail (c M : ℝ) (hc : 0 < c) :
    ∃ k : ℕ, 1 ≤ k ∧ ∀ n : ℕ, k < n → M < c * (n : ℝ) ^ 2 := by
  obtain ⟨k, hk⟩ := exists_nat_gt (max 1 (M / c))
  have hk1 : (1 : ℝ) < k := lt_of_le_of_lt (le_max_left _ _) hk
  have hkn : 1 < k := by exact_mod_cast hk1
  refine ⟨k, hkn.le, ?_⟩
  intro n hn
  have hnr : (k : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) < n := hk1.trans hnr
  have hratio : M / c < n := (lt_of_le_of_lt (le_max_right _ _) hk).trans hnr
  have hM : M < (n : ℝ) * c := (div_lt_iff₀ hc).mp hratio
  have hs : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hs hc.le
  nlinarith

/-- For a map continuous at positive points, its values at the discrete
eigenvalues of a fixed mode converge to its value at the continuum eigenvalue. -/
theorem comp_discreteNeumannEigenvalue_tendsto (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, 0 < x → ContinuousAt f x)
    (L : ℝ) (n : ℕ) (hL : 0 < L) (hn : 0 < n) :
    Tendsto (fun N : ℕ => f (discreteNeumannEigenvalue L n N)) atTop
      (𝓝 (f (neumannEigenvalue L n))) := by
  have hlam : 0 < neumannEigenvalue L n := by
    unfold neumannEigenvalue
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  exact (hf _ hlam).tendsto.comp (discreteNeumannEigenvalue_tendsto L n hL hn)

/-- Uniform discrete cutoff: for all sufficiently fine meshes, every mode
`k < n ≤ N` has a value strictly larger than the first mode. -/
theorem exists_uniform_discrete_tail (f : ℝ → ℝ) (K L : ℝ)
    (hK : 0 < K) (hL : 0 < L)
    (hf : ∀ x : ℝ, 0 < x → ContinuousAt f x)
    (hlow : ∀ x : ℝ, 0 < x → K * x ≤ f x) :
    ∃ k : ℕ, 1 ≤ k ∧ ∀ᶠ N in atTop,
      ∀ n : ℕ, k < n → n ≤ N →
        f (discreteNeumannEigenvalue L 1 N) < f (discreteNeumannEigenvalue L n N) := by
  let M := f (neumannEigenvalue L 1) + 1
  have hfirst := comp_discreteNeumannEigenvalue_tendsto f hf L 1 hL Nat.one_pos
  have hbounded : ∀ᶠ N in atTop, f (discreteNeumannEigenvalue L 1 N) < M :=
    hfirst.eventually (gt_mem_nhds (by dsimp [M]; linarith))
  obtain ⟨k, hk, htail⟩ := exists_quadratic_tail (4 * K / L ^ 2) M (by positivity)
  refine ⟨k, hk, ?_⟩
  filter_upwards [hbounded, eventually_gt_atTop (0 : ℕ)] with N hNbound hN
  intro n hkn hnN
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (hk.trans hkn.le)
  have hlower := discreteNeumannEigenvalue_lower_bound L n N hL hN hnN
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlam : 0 < discreteNeumannEigenvalue L n N := lt_of_lt_of_le (by positivity) hlower
  have hscaled : (4 * K / L ^ 2) * (n : ℝ) ^ 2 ≤ K * discreteNeumannEigenvalue L n N := by
    calc
      (4 * K / L ^ 2) * (n : ℝ) ^ 2 = K * (4 * (n : ℝ) ^ 2 / L ^ 2) := by ring
      _ ≤ K * discreteNeumannEigenvalue L n N := mul_le_mul_of_nonneg_left hlower hK.le
  exact hNbound.trans ((htail n hkn).trans_le (hscaled.trans (hlow _ hlam)))

/-- Uniform continuum cutoff: every mode `n > k` has a value strictly larger
than the first mode. -/
theorem exists_uniform_continuum_tail (f : ℝ → ℝ) (K L : ℝ)
    (hK : 0 < K) (hL : 0 < L)
    (hlow : ∀ x : ℝ, 0 < x → K * x ≤ f x) :
    ∃ k : ℕ, 1 ≤ k ∧ ∀ n : ℕ, k < n →
      f (neumannEigenvalue L 1) < f (neumannEigenvalue L n) := by
  obtain ⟨k, hk, htail⟩ := exists_quadratic_tail
    (K * Real.pi ^ 2 / L ^ 2) (f (neumannEigenvalue L 1)) (by positivity)
  refine ⟨k, hk, ?_⟩
  intro n hkn
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (hk.trans hkn.le)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlam : 0 < neumannEigenvalue L n := by unfold neumannEigenvalue; positivity
  have hid : K * Real.pi ^ 2 / L ^ 2 * (n : ℝ) ^ 2 = K * neumannEigenvalue L n := by
    unfold neumannEigenvalue
    ring
  apply (htail n hkn).trans_le
  rw [hid]
  exact hlow _ hlam

/-- A finite minimum is unchanged after removing indices whose values are at
least that of a retained index. -/
theorem finset_inf'_eq_of_tail {S T : Finset ℕ}
    (hS : S.Nonempty) (hT : T.Nonempty) (hsub : S ⊆ T)
    (f : ℕ → ℝ) (j : ℕ) (hj : j ∈ S)
    (htail : ∀ n ∈ T, n ∉ S → f j ≤ f n) :
    T.inf' hT f = S.inf' hS f := by
  apply le_antisymm
  · apply Finset.le_inf' hS f
    intro n hn
    exact Finset.inf'_le f (hsub hn)
  · apply Finset.le_inf' hT f
    intro n hn
    by_cases hnS : n ∈ S
    · exact Finset.inf'_le f hnS
    · exact (Finset.inf'_le f hj).trans (htail n hn hnS)

end NeumannCosine.Discrete.ModalMinimumTail
