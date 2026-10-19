/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import NeumannCosine.Discrete.ModalMinimumTail

/-!
# Convergence of the discrete modal minimum

Let `f : ℝ → ℝ` be continuous at every positive point and satisfy
`K * x ≤ f x` for `x > 0`, with `K > 0`. No additional sign, monotonicity or
convexity assumption on `f` is needed.

The discrete modal minimum is the minimum of `f` over the discrete Neumann
eigenvalues of the modes `1 ≤ n ≤ N`. The continuum modal infimum is the
infimum of `f` over the continuum Neumann eigenvalues of all modes `n ≥ 1`.
The main theorem `discreteModalMin_tendsto` shows that the first converges to
the second as `N → ∞`. The proof combines the uniform tail cutoffs with
fixed-mode convergence over a finite set of modes.
-/

@[expose] public section

set_option autoImplicit false

namespace NeumannCosine.Discrete.ModalMinimumLimit

open Filter
open scoped Topology
open NeumannCosine.Discrete.Eigenvalues
open NeumannCosine.Discrete.ModalMinimumTail

noncomputable section

/-- The positive modes `1, …, N` represented on a mesh with `N` intervals. -/
def positiveModes (N : ℕ) : Finset ℕ := Finset.Icc 1 N

theorem positiveModes_nonempty {N : ℕ} (hN : 0 < N) : (positiveModes N).Nonempty :=
  ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hN⟩⟩

/-- Discrete modal minimum of `f` over the modes `1 ≤ n ≤ N`, with value `0`
when `N = 0`. -/
def discreteModalMin (f : ℝ → ℝ) (L : ℝ) (N : ℕ) : ℝ :=
  if hN : 0 < N then
    (positiveModes N).inf' (positiveModes_nonempty hN)
      (fun n => f (discreteNeumannEigenvalue L n N))
  else 0

/-- Continuum modal infimum of `f` over all modes `n ≥ 1`. -/
def continuumModalInf (f : ℝ → ℝ) (L : ℝ) : ℝ :=
  sInf {y : ℝ | ∃ n : ℕ, 1 ≤ n ∧ y = f (neumannEigenvalue L n)}

/-- A continuum tail estimate identifies the infimum over all positive modes
with a finite minimum. -/
theorem continuumModalInf_eq_finset_inf' (f : ℝ → ℝ) (L : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (htail : ∀ n : ℕ, k < n → f (neumannEigenvalue L 1) ≤ f (neumannEigenvalue L n)) :
    continuumModalInf f L =
      (positiveModes k).inf' (positiveModes_nonempty hk)
        (fun n => f (neumannEigenvalue L n)) := by
  let g : ℕ → ℝ := fun n => f (neumannEigenvalue L n)
  have hne := positiveModes_nonempty hk
  have hleast : IsLeast {y : ℝ | ∃ n : ℕ, 1 ≤ n ∧ y = g n}
      ((positiveModes k).inf' hne g) := by
    constructor
    · obtain ⟨n, hn, heq⟩ := Finset.exists_mem_eq_inf' hne g
      exact ⟨n, (Finset.mem_Icc.mp hn).1, heq⟩
    · rintro y ⟨n, hn, rfl⟩
      by_cases hnk : n ≤ k
      · exact Finset.inf'_le g (Finset.mem_Icc.mpr ⟨hn, hnk⟩)
      · exact (Finset.inf'_le g (Finset.mem_Icc.mpr ⟨le_rfl, hk⟩)).trans
          (htail n (lt_of_not_ge hnk))
  exact hleast.csInf_eq

/-- **Modal-minimum convergence.** If `f` is continuous at every positive
point and `K * x ≤ f x` for `x > 0` with `K > 0`, then the discrete minimum
over the modes `1 ≤ n ≤ N` converges to the continuum infimum over the modes
`n ≥ 1`. -/
theorem discreteModalMin_tendsto (f : ℝ → ℝ) (K L : ℝ)
    (hK : 0 < K) (hL : 0 < L)
    (hf : ∀ x : ℝ, 0 < x → ContinuousAt f x)
    (hlow : ∀ x : ℝ, 0 < x → K * x ≤ f x) :
    Tendsto (discreteModalMin f L) atTop (𝓝 (continuumModalInf f L)) := by
  obtain ⟨kd, hkd, hd⟩ := exists_uniform_discrete_tail f K L hK hL hf hlow
  obtain ⟨kc, hkc, hc⟩ := exists_uniform_continuum_tail f K L hK hL hlow
  let k := max kd kc
  have hk : 1 ≤ k := hkd.trans (le_max_left _ _)
  have hne := positiveModes_nonempty hk
  have hlimit : continuumModalInf f L =
      (positiveModes k).inf' hne (fun n => f (neumannEigenvalue L n)) :=
    continuumModalInf_eq_finset_inf' f L k hk (fun n hn =>
      (hc n (lt_of_le_of_lt (le_max_right _ _) hn)).le)
  have hfin : Tendsto
      (fun N => (positiveModes k).inf' hne (fun n => f (discreteNeumannEigenvalue L n N)))
      atTop (𝓝 ((positiveModes k).inf' hne (fun n => f (neumannEigenvalue L n)))) := by
    apply Filter.Tendsto.finset_inf'_nhds_apply hne
    intro n hn
    exact comp_discreteNeumannEigenvalue_tendsto f hf L n hL (Finset.mem_Icc.mp hn).1
  rw [hlimit]
  apply hfin.congr'
  filter_upwards [hd, eventually_ge_atTop k] with N hNtail hkN
  have hN : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (hk.trans hkN)
  unfold discreteModalMin
  rw [dif_pos hN]
  symm
  apply finset_inf'_eq_of_tail hne (positiveModes_nonempty hN) (j := 1)
  · intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans hkN⟩
  · exact Finset.mem_Icc.mpr ⟨le_rfl, hk⟩
  · intro n hn hnS
    have hnk : k < n := by
      by_contra h
      exact hnS (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, le_of_not_gt h⟩)
    exact (hNtail n (lt_of_le_of_lt (le_max_left _ _) hnk) (Finset.mem_Icc.mp hn).2).le

end

end NeumannCosine.Discrete.ModalMinimumLimit
