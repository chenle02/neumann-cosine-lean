module
/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/

public import NeumannCosine.Basic

@[expose] public section

/-!
# Integrals of products of three and four Neumann modes

We compute exactly the integrals over `[0, L]` of products of the Neumann
modes `cos (i π x / L)` and the sine modes `sin (n π x / L)`:

* one cosine against two sines, `∫ cos_i sin_n sin_k`;
* three cosines, `∫ cos_i cos_j cos_k`;
* two cosines against two sines, `∫ cos_i cos_j sin_n sin_k`;
* four cosines, `∫ cos_i cos_j cos_l cos_k`.

Each integral is a finite sum of indicator terms. The *signed* form holds for
all natural indices: there is one indicator per product-to-sum term, with
conditions `i ± j ± ... = 0` over `ℤ`. The *constrained* form writes every
condition as an equation between integer casts of the natural indices, and
the zero-mode multiplicity is an explicit extra indicator.
-/

set_option autoImplicit false

namespace NeumannCosine.KernelIntegrals

noncomputable section

/-- The sine mode `sin (n π x / L)`. Up to the factor `-n π / L`, it is the
derivative of the Neumann mode `cos (n π x / L)`. -/
def sinMode (L : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.sin ((n : ℝ) * Real.pi * x / L)

/-- The cosine with a signed integer index, `cos (m π x / L)`, `m ∈ ℤ`. -/
def intMode (L : ℝ) (m : ℤ) (x : ℝ) : ℝ :=
  Real.cos ((m : ℝ) * Real.pi * x / L)

/-- Real-valued indicator of a decidable proposition. -/
def indicatorR (P : Prop) [Decidable P] : ℝ :=
  if P then 1 else 0

theorem continuous_intMode (L : ℝ) (m : ℤ) :
    Continuous (intMode L m) := by
  unfold intMode
  fun_prop

/-- Basic kernel: `∫₀ᴸ cos (m π x / L) dx = L · 1_{m = 0}` for `m ∈ ℤ`. -/
theorem integral_intMode (L : ℝ) (hL : 0 < L) (m : ℤ) :
    (∫ x in (0 : ℝ)..L, intMode L m x) = L * indicatorR (m = 0) := by
  have h : ∀ x : ℝ, intMode L m x =
      Real.cos (((m : ℝ) * Real.pi / L) * x) := by
    intro x
    unfold intMode
    congr 1
    ring
  simp only [h]
  rw [NeumannCosine.integral_cos_int_mul_pi_div L hL m, indicatorR]
  split_ifs <;> ring

private theorem integral_term (L : ℝ) (hL : 0 < L) (c : ℝ) (m : ℤ) :
    (∫ x in (0 : ℝ)..L, c * intMode L m x) = c * (L * indicatorR (m = 0)) := by
  rw [intervalIntegral.integral_const_mul, integral_intMode L hL]

private theorem integral_add_term (L : ℝ) (hL : 0 < L) (f : ℝ → ℝ)
    (hf : Continuous f) (c : ℝ) (m : ℤ) :
    (∫ x in (0 : ℝ)..L, (f x + c * intMode L m x)) =
      (∫ x in (0 : ℝ)..L, f x) + c * (L * indicatorR (m = 0)) := by
  rw [intervalIntegral.integral_add (f := f)
    (g := fun x => c * intMode L m x) (hf.intervalIntegrable _ _)
    ((continuous_const.mul (continuous_intMode L m)).intervalIntegrable _ _),
    integral_term L hL]

/-- Integral of a four-term signed cosine combination. -/
theorem integral_four_intMode (L : ℝ) (hL : 0 < L)
    (c₁ c₂ c₃ c₄ : ℝ) (m₁ m₂ m₃ m₄ : ℤ) :
    (∫ x in (0 : ℝ)..L,
      (c₁ * intMode L m₁ x + c₂ * intMode L m₂ x +
        c₃ * intMode L m₃ x + c₄ * intMode L m₄ x)) =
      L * (c₁ * indicatorR (m₁ = 0) + c₂ * indicatorR (m₂ = 0) +
        c₃ * indicatorR (m₃ = 0) + c₄ * indicatorR (m₄ = 0)) := by
  rw [integral_add_term L hL, integral_add_term L hL, integral_add_term L hL,
    integral_term L hL]
  · ring
  all_goals
    unfold intMode
    fun_prop

/-- Integral of an eight-term signed cosine combination. -/
theorem integral_eight_intMode (L : ℝ) (hL : 0 < L)
    (c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ : ℝ) (m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ : ℤ) :
    (∫ x in (0 : ℝ)..L,
      (c₁ * intMode L m₁ x + c₂ * intMode L m₂ x +
        c₃ * intMode L m₃ x + c₄ * intMode L m₄ x +
        c₅ * intMode L m₅ x + c₆ * intMode L m₆ x +
        c₇ * intMode L m₇ x + c₈ * intMode L m₈ x)) =
      L * (c₁ * indicatorR (m₁ = 0) + c₂ * indicatorR (m₂ = 0) +
        c₃ * indicatorR (m₃ = 0) + c₄ * indicatorR (m₄ = 0) +
        c₅ * indicatorR (m₅ = 0) + c₆ * indicatorR (m₆ = 0) +
        c₇ * indicatorR (m₇ = 0) + c₈ * indicatorR (m₈ = 0)) := by
  rw [integral_add_term L hL, integral_add_term L hL, integral_add_term L hL,
    integral_add_term L hL, integral_add_term L hL, integral_add_term L hL,
    integral_add_term L hL, integral_term L hL]
  · ring
  all_goals
    unfold intMode
    fun_prop

/-! ### Pointwise product-to-sum identities -/

private theorem phase_mul (L x a : ℝ) :
    a * Real.pi * x / L = a * (Real.pi * x / L) := by
  ring

/-- `cos_i sin_n sin_k` as a signed four-term cosine combination. -/
theorem cos_sin_sin_eq (L : ℝ) (i n k : ℕ) (x : ℝ) :
    mode L i x * sinMode L n x * sinMode L k x =
      (1 / 4) * intMode L ((i : ℤ) + n - k) x +
        (1 / 4) * intMode L ((i : ℤ) - n + k) x +
        (-1 / 4) * intMode L ((i : ℤ) + n + k) x +
        (-1 / 4) * intMode L ((i : ℤ) - n - k) x := by
  unfold mode sinMode intMode
  push_cast
  simp only [phase_mul L x]
  generalize Real.pi * x / L = t
  simp only [add_mul, sub_mul, Real.cos_add, Real.cos_sub, Real.sin_add,
    Real.sin_sub]
  ring

/-- `cos_i cos_j cos_k` as a signed four-term cosine combination. -/
theorem cos_cos_cos_eq (L : ℝ) (i j k : ℕ) (x : ℝ) :
    mode L i x * mode L j x * mode L k x =
      (1 / 4) * intMode L ((i : ℤ) + j + k) x +
        (1 / 4) * intMode L ((i : ℤ) + j - k) x +
        (1 / 4) * intMode L ((i : ℤ) - j + k) x +
        (1 / 4) * intMode L ((i : ℤ) - j - k) x := by
  unfold mode intMode
  push_cast
  simp only [phase_mul L x]
  generalize Real.pi * x / L = t
  simp only [add_mul, sub_mul, Real.cos_add, Real.cos_sub, Real.sin_add,
    Real.sin_sub]
  ring

/-- `cos_i cos_j sin_n sin_k` as a signed eight-term cosine combination. -/
theorem cos_cos_sin_sin_eq (L : ℝ) (i j n k : ℕ) (x : ℝ) :
    mode L i x * mode L j x * sinMode L n x *
        sinMode L k x =
      (1 / 8) * intMode L ((i : ℤ) + j + n - k) x +
        (1 / 8) * intMode L ((i : ℤ) + j - n + k) x +
        (1 / 8) * intMode L ((i : ℤ) - j + n - k) x +
        (1 / 8) * intMode L ((i : ℤ) - j - n + k) x +
        (-1 / 8) * intMode L ((i : ℤ) + j + n + k) x +
        (-1 / 8) * intMode L ((i : ℤ) + j - n - k) x +
        (-1 / 8) * intMode L ((i : ℤ) - j + n + k) x +
        (-1 / 8) * intMode L ((i : ℤ) - j - n - k) x := by
  unfold mode sinMode intMode
  push_cast
  simp only [phase_mul L x]
  generalize Real.pi * x / L = t
  simp only [add_mul, sub_mul, Real.cos_add, Real.cos_sub, Real.sin_add,
    Real.sin_sub]
  ring

/-- `cos_i cos_j cos_l cos_k` as a signed eight-term cosine combination. -/
theorem cos_cos_cos_cos_eq (L : ℝ) (i j l k : ℕ) (x : ℝ) :
    mode L i x * mode L j x * mode L l x *
        mode L k x =
      (1 / 8) * intMode L ((i : ℤ) + j + l + k) x +
        (1 / 8) * intMode L ((i : ℤ) + j + l - k) x +
        (1 / 8) * intMode L ((i : ℤ) + j - l + k) x +
        (1 / 8) * intMode L ((i : ℤ) + j - l - k) x +
        (1 / 8) * intMode L ((i : ℤ) - j + l + k) x +
        (1 / 8) * intMode L ((i : ℤ) - j + l - k) x +
        (1 / 8) * intMode L ((i : ℤ) - j - l + k) x +
        (1 / 8) * intMode L ((i : ℤ) - j - l - k) x := by
  unfold mode intMode
  push_cast
  simp only [phase_mul L x]
  generalize Real.pi * x / L = t
  simp only [add_mul, sub_mul, Real.cos_add, Real.cos_sub, Real.sin_add,
    Real.sin_sub]
  ring

/-! ### Signed kernel integrals (all natural indices, including zero modes) -/

/-- Signed form of the one-cosine/two-sine kernel; valid for all `i n k`. -/
theorem integral_cos_sin_sin_signed (L : ℝ) (hL : 0 < L) (i n k : ℕ) :
    (∫ x in (0 : ℝ)..L,
      mode L i x * sinMode L n x * sinMode L k x) =
      L / 4 * (indicatorR ((i : ℤ) + n - k = 0) + indicatorR ((i : ℤ) - n + k = 0) -
        indicatorR ((i : ℤ) + n + k = 0) - indicatorR ((i : ℤ) - n - k = 0)) := by
  rw [intervalIntegral.integral_congr (fun x _ => cos_sin_sin_eq L i n k x),
    integral_four_intMode L hL]
  ring

/-- Signed form of the three-cosine kernel; valid for all `i j k`. -/
theorem integral_cos_cos_cos_signed (L : ℝ) (hL : 0 < L) (i j k : ℕ) :
    (∫ x in (0 : ℝ)..L,
      mode L i x * mode L j x * mode L k x) =
      L / 4 * (indicatorR ((i : ℤ) + j + k = 0) + indicatorR ((i : ℤ) + j - k = 0) +
        indicatorR ((i : ℤ) - j + k = 0) + indicatorR ((i : ℤ) - j - k = 0)) := by
  rw [intervalIntegral.integral_congr (fun x _ => cos_cos_cos_eq L i j k x),
    integral_four_intMode L hL]
  ring

/-- Signed form of the two-cosine/two-sine kernel; valid for all `i j n k`. -/
theorem integral_cos_cos_sin_sin_signed (L : ℝ) (hL : 0 < L) (i j n k : ℕ) :
    (∫ x in (0 : ℝ)..L,
      mode L i x * mode L j x * sinMode L n x *
        sinMode L k x) =
      L / 8 * (indicatorR ((i : ℤ) + j + n - k = 0) + indicatorR ((i : ℤ) + j - n + k = 0) +
        indicatorR ((i : ℤ) - j + n - k = 0) + indicatorR ((i : ℤ) - j - n + k = 0) -
        indicatorR ((i : ℤ) + j + n + k = 0) - indicatorR ((i : ℤ) + j - n - k = 0) -
        indicatorR ((i : ℤ) - j + n + k = 0) - indicatorR ((i : ℤ) - j - n - k = 0)) := by
  rw [intervalIntegral.integral_congr
      (fun x _ => cos_cos_sin_sin_eq L i j n k x),
    integral_eight_intMode L hL]
  ring

/-- Signed form of the four-cosine kernel; valid for all `i j l k`. -/
theorem integral_cos_cos_cos_cos_signed (L : ℝ) (hL : 0 < L) (i j l k : ℕ) :
    (∫ x in (0 : ℝ)..L,
      mode L i x * mode L j x * mode L l x *
        mode L k x) =
      L / 8 * (indicatorR ((i : ℤ) + j + l + k = 0) + indicatorR ((i : ℤ) + j + l - k = 0) +
        indicatorR ((i : ℤ) + j - l + k = 0) + indicatorR ((i : ℤ) + j - l - k = 0) +
        indicatorR ((i : ℤ) - j + l + k = 0) + indicatorR ((i : ℤ) - j + l - k = 0) +
        indicatorR ((i : ℤ) - j - l + k = 0) + indicatorR ((i : ℤ) - j - l - k = 0)) := by
  rw [intervalIntegral.integral_congr
      (fun x _ => cos_cos_cos_cos_eq L i j l k x),
    integral_eight_intMode L hL]
  ring

/-! ### Kernel integrals in constrained form -/

private theorem indicatorR_congr {P Q : Prop} [Decidable P] [Decidable Q]
    (h : P ↔ Q) : indicatorR P = indicatorR Q := by
  unfold indicatorR
  by_cases hQ : Q
  · simp [hQ, h.mpr hQ]
  · simp [hQ, mt h.mp hQ]

private theorem indicatorR_false {P : Prop} [Decidable P] (h : ¬P) : indicatorR P = 0 := by
  unfold indicatorR
  simp [h]

/-- The one-cosine/two-sine kernel: for `n, k ≥ 1`, the coefficient of `u_i`
is `(L/4)(1_{i=|n-k|} - 1_{i=n+k} + δ_{nk} 1_{i=0})`. -/
theorem integral_cos_sin_sin (L : ℝ) (hL : 0 < L) (i n k : ℕ)
    (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (∫ x in (0 : ℝ)..L,
      mode L i x * sinMode L n x * sinMode L k x) =
      L / 4 * (indicatorR (i = Int.natAbs ((n : ℤ) - k)) - indicatorR (i = n + k) +
        indicatorR (n = k ∧ i = 0)) := by
  rw [integral_cos_sin_sin_signed L hL i n k,
    indicatorR_false (P := (i : ℤ) + n + k = 0) (by omega),
    indicatorR_congr (P := (i : ℤ) - n - k = 0) (Q := i = n + k) (by omega)]
  have key : indicatorR ((i : ℤ) + n - k = 0) + indicatorR ((i : ℤ) - n + k = 0) =
      indicatorR (i = Int.natAbs ((n : ℤ) - k)) + indicatorR (n = k ∧ i = 0) := by
    have habs := Int.natAbs_eq ((n : ℤ) - k)
    unfold indicatorR
    generalize Int.natAbs ((n : ℤ) - k) = a at habs ⊢
    split_ifs <;> first | (exfalso; omega) | norm_num
  rw [show indicatorR ((i : ℤ) + n - k = 0) + indicatorR ((i : ℤ) - n + k = 0) - 0 -
      indicatorR (i = n + k) =
      (indicatorR ((i : ℤ) + n - k = 0) + indicatorR ((i : ℤ) - n + k = 0)) -
        indicatorR (i = n + k) by ring, key]
  ring

/-- The three-cosine kernel: for all `k ≥ 0`, the coefficient of `u_i v_j` is
`(L/4)(1_{i-j=k} + 1_{i-j=-k} + 1_{i+j=k}) + (L/4) 1_{k=0} 1_{i=0} 1_{j=0}`. -/
theorem integral_cos_cos_cos (L : ℝ) (hL : 0 < L) (i j k : ℕ) :
    (∫ x in (0 : ℝ)..L,
      mode L i x * mode L j x * mode L k x) =
      L / 4 * (indicatorR ((i : ℤ) - j = k) + indicatorR ((i : ℤ) - j = -k) +
        indicatorR ((i : ℤ) + j = k)) +
        L / 4 * indicatorR (k = 0 ∧ i = 0 ∧ j = 0) := by
  rw [integral_cos_cos_cos_signed L hL i j k,
    indicatorR_congr (P := (i : ℤ) + j + k = 0) (Q := k = 0 ∧ i = 0 ∧ j = 0)
      (by omega),
    indicatorR_congr (P := (i : ℤ) + j - k = 0) (Q := (i : ℤ) + j = k) (by omega),
    indicatorR_congr (P := (i : ℤ) - j + k = 0) (Q := (i : ℤ) - j = -k) (by omega),
    indicatorR_congr (P := (i : ℤ) - j - k = 0) (Q := (i : ℤ) - j = k) (by omega)]
  ring

/-- The two-cosine/two-sine kernel: for `n, k ≥ 1`, the coefficient of
`u_i v_j` is `(L/8)` times seven signed indicators. The eighth product-to-sum
term `i+j = -(n+k)` vanishes because `n + k ≥ 2`. -/
theorem integral_cos_cos_sin_sin (L : ℝ) (hL : 0 < L) (i j n k : ℕ)
    (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (∫ x in (0 : ℝ)..L,
      mode L i x * mode L j x * sinMode L n x *
        sinMode L k x) =
      L / 8 * (indicatorR ((i : ℤ) - j = (n : ℤ) - k) +
        indicatorR ((i : ℤ) - j = -((n : ℤ) - k)) +
        indicatorR ((i : ℤ) + j = (n : ℤ) - k) +
        indicatorR ((i : ℤ) + j = -((n : ℤ) - k)) -
        indicatorR ((i : ℤ) - j = (n : ℤ) + k) -
        indicatorR ((i : ℤ) - j = -((n : ℤ) + k)) -
        indicatorR ((i : ℤ) + j = (n : ℤ) + k)) := by
  rw [integral_cos_cos_sin_sin_signed L hL i j n k,
    indicatorR_congr (P := (i : ℤ) + j + n - k = 0)
      (Q := (i : ℤ) + j = -((n : ℤ) - k)) (by omega),
    indicatorR_congr (P := (i : ℤ) + j - n + k = 0)
      (Q := (i : ℤ) + j = (n : ℤ) - k) (by omega),
    indicatorR_congr (P := (i : ℤ) - j + n - k = 0)
      (Q := (i : ℤ) - j = -((n : ℤ) - k)) (by omega),
    indicatorR_congr (P := (i : ℤ) - j - n + k = 0)
      (Q := (i : ℤ) - j = (n : ℤ) - k) (by omega),
    indicatorR_false (P := (i : ℤ) + j + n + k = 0) (by omega),
    indicatorR_congr (P := (i : ℤ) + j - n - k = 0)
      (Q := (i : ℤ) + j = (n : ℤ) + k) (by omega),
    indicatorR_congr (P := (i : ℤ) - j + n + k = 0)
      (Q := (i : ℤ) - j = -((n : ℤ) + k)) (by omega),
    indicatorR_congr (P := (i : ℤ) - j - n - k = 0)
      (Q := (i : ℤ) - j = (n : ℤ) + k) (by omega)]
  ring

/-- The four-cosine kernel: for all `k ≥ 0`, the coefficient of `u_i v_j w_l`
is `(L/8)` times seven signed indicators plus `(L/8) 1_{k=0} 1_{i=j=l=0}`. -/
theorem integral_cos_cos_cos_cos (L : ℝ) (hL : 0 < L) (i j l k : ℕ) :
    (∫ x in (0 : ℝ)..L,
      mode L i x * mode L j x * mode L l x *
        mode L k x) =
      L / 8 * (indicatorR ((i : ℤ) + j + l = k) + indicatorR ((i : ℤ) + j - l = k) +
        indicatorR ((i : ℤ) + j - l = -k) + indicatorR ((i : ℤ) - j + l = k) +
        indicatorR ((i : ℤ) - j + l = -k) + indicatorR ((i : ℤ) - j - l = k) +
        indicatorR ((i : ℤ) - j - l = -k)) +
        L / 8 * indicatorR (k = 0 ∧ i = 0 ∧ j = 0 ∧ l = 0) := by
  rw [integral_cos_cos_cos_cos_signed L hL i j l k,
    indicatorR_congr (P := (i : ℤ) + j + l + k = 0)
      (Q := k = 0 ∧ i = 0 ∧ j = 0 ∧ l = 0) (by omega),
    indicatorR_congr (P := (i : ℤ) + j + l - k = 0)
      (Q := (i : ℤ) + j + l = k) (by omega),
    indicatorR_congr (P := (i : ℤ) + j - l + k = 0)
      (Q := (i : ℤ) + j - l = -k) (by omega),
    indicatorR_congr (P := (i : ℤ) + j - l - k = 0)
      (Q := (i : ℤ) + j - l = k) (by omega),
    indicatorR_congr (P := (i : ℤ) - j + l + k = 0)
      (Q := (i : ℤ) - j + l = -k) (by omega),
    indicatorR_congr (P := (i : ℤ) - j + l - k = 0)
      (Q := (i : ℤ) - j + l = k) (by omega),
    indicatorR_congr (P := (i : ℤ) - j - l + k = 0)
      (Q := (i : ℤ) - j - l = -k) (by omega),
    indicatorR_congr (P := (i : ℤ) - j - l - k = 0)
      (Q := (i : ℤ) - j - l = k) (by omega)]
  ring

/-! ### The zero-mode terms are needed

Dropping the explicit zero-mode term from each constrained formula gives a
false value at the smallest instance. -/

/-- Without `δ_{nk} u_0`, the one-cosine/two-sine kernel at `i = 0`,
`n = k = 1` would be `L/4`; the true value is `L/2`. -/
theorem integral_cos_sin_sin_zero_mode (L : ℝ) (hL : 0 < L) :
    (∫ x in (0 : ℝ)..L,
      mode L 0 x * sinMode L 1 x * sinMode L 1 x) = L / 2 ∧
    (∫ x in (0 : ℝ)..L,
      mode L 0 x * sinMode L 1 x * sinMode L 1 x) ≠ L / 4 := by
  rw [integral_cos_sin_sin L hL 0 1 1 le_rfl le_rfl]
  simp only [indicatorR]
  norm_num
  constructor
  · ring
  · intro h
    linarith

/-- Without `1_{k=0} u_0 v_0`, the three-cosine kernel at `i = j = k = 0`
would be `3L/4`; the true value is `L`. -/
theorem integral_cos_cos_cos_zero_mode (L : ℝ) (hL : 0 < L) :
    (∫ x in (0 : ℝ)..L,
      mode L 0 x * mode L 0 x * mode L 0 x) = L ∧
    (∫ x in (0 : ℝ)..L,
      mode L 0 x * mode L 0 x * mode L 0 x) ≠
      3 * L / 4 := by
  rw [integral_cos_cos_cos L hL 0 0 0]
  simp only [indicatorR]
  norm_num
  constructor
  · ring
  · intro h
    linarith

/-- Without `1_{k=0} u_0 v_0 w_0`, the four-cosine kernel at
`i = j = l = k = 0` would be `7L/8`; the true value is `L`. -/
theorem integral_cos_cos_cos_cos_zero_mode (L : ℝ) (hL : 0 < L) :
    (∫ x in (0 : ℝ)..L,
      mode L 0 x * mode L 0 x * mode L 0 x *
        mode L 0 x) = L ∧
    (∫ x in (0 : ℝ)..L,
      mode L 0 x * mode L 0 x * mode L 0 x *
        mode L 0 x) ≠ 7 * L / 8 := by
  rw [integral_cos_cos_cos_cos L hL 0 0 0 0]
  simp only [indicatorR]
  norm_num
  constructor
  · ring
  · intro h
    linarith

end

end NeumannCosine.KernelIntegrals
