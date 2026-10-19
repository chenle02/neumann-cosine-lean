module
/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/

public import NeumannCosine.Series.TermwiseIntegral

@[expose] public section

/-!
# Products of cosine series and signed-index reindexing

This file gives the series steps behind the integral identities for products
of cosine series on `[0, L]`.

1. *Product of separately summed series.*  For absolutely summable
   coefficient families and phases of norm at most one, the product of the
   separately summed series is the tsum over the product index
   (`tsum_mul_tsum_bounded`, `cosineSeries_mul_cosineSeries`,
   `cosineSeries_mul_cosineSeries_mul_cosineSeries`).
2. *Interchange with the integral.*  The product-index tsum commutes with the
   interval integral against a bounded continuous kernel, and the
   coefficient leaves the integral (`hasSum_integral_tsum_mul`,
   `hasSum_integral_tsum_mul_tsum`, and the cosine specializations).  All
   summability is derived from the `ℓ¹` hypotheses and the uniform bounds; it
   is never assumed.
3. *Signed-index reindexing.*  A product-index sum weighted by the indicator
   of a signed constraint is the constrained sum, read as a tsum over the
   subtype of indices that satisfy the constraint (`hasSum_mul_ite`).
   Differences are integer differences: every constraint is stated after
   casting the natural indices to `ℤ`.  Degenerate constraints collapse with
   exact multiplicity (`hasSum_mul_ite_int_eq`, `hasSum_pair_ite_add_eq_neg`,
   `hasSum_triple_ite_add_add_eq_neg`).

The four product identities are then proved *conditionally* on the
closed-form kernel integrals, in the raw product-to-sum indicator form (all
`2^(m-1)` signed constraints, including the empty and degenerate ones).  The
kernel integrals themselves are computed in `NeumannCosine.KernelIntegrals`.
-/

set_option autoImplicit false

namespace NeumannCosine.Series.Products

open MeasureTheory Set
open NeumannCosine.Series.TermwiseIntegral

noncomputable section

/-! ### Step 1: products of separately summed series -/

/-- A coefficient family against factors of norm at most one stays
absolutely summable. -/
theorem summable_norm_mul_bounded {ι : Type*} (c f : ι → ℝ)
    (hc : Summable fun i => ‖c i‖) (hf : ∀ i, ‖f i‖ ≤ 1) :
    Summable fun i => ‖c i * f i‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun i => by
      rw [norm_mul]
      simpa using mul_le_mul_of_nonneg_left (hf i) (norm_nonneg (c i)))
    hc

/-- The product of two separately summed series with bounded factors equals
the tsum over the product index. -/
theorem tsum_mul_tsum_bounded {ι ι' : Type*} (u : ι → ℝ) (v : ι' → ℝ)
    (f : ι → ℝ) (g : ι' → ℝ)
    (hu : Summable fun i => ‖u i‖) (hv : Summable fun j => ‖v j‖)
    (hf : ∀ i, ‖f i‖ ≤ 1) (hg : ∀ j, ‖g j‖ ≤ 1) :
    (∑' i, u i * f i) * (∑' j, v j * g j) =
      ∑' p : ι × ι', (u p.1 * v p.2) * (f p.1 * g p.2) := by
  rw [tsum_mul_tsum_of_summable_norm (summable_norm_mul_bounded u f hu hf)
    (summable_norm_mul_bounded v g hv hg)]
  congr 1
  funext p
  ring

theorem norm_cos_phase_le_one (L : ℝ) (n : ℕ) (x : ℝ) :
    ‖Real.cos ((n : ℝ) * Real.pi * x / L)‖ ≤ 1 := by
  simpa only [Real.norm_eq_abs] using
    Real.abs_cos_le_one ((n : ℝ) * Real.pi * x / L)

theorem norm_cos_phase_mul_le_one (L : ℝ) (q : ℕ × ℕ) (x : ℝ) :
    ‖Real.cos ((q.1 : ℝ) * Real.pi * x / L) *
      Real.cos ((q.2 : ℝ) * Real.pi * x / L)‖ ≤ 1 := by
  rw [norm_mul]
  simpa only [one_mul] using mul_le_mul (norm_cos_phase_le_one L q.1 x)
    (norm_cos_phase_le_one L q.2 x) (norm_nonneg _) (by norm_num)

/-- Product of two absolutely summable cosine series, pointwise. -/
theorem cosineSeries_mul_cosineSeries (L : ℝ) (u v : ℕ → ℝ)
    (hu : Summable fun i => ‖u i‖) (hv : Summable fun j => ‖v j‖) (x : ℝ) :
    (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
        (∑' j : ℕ, v j * Real.cos ((j : ℝ) * Real.pi * x / L)) =
      ∑' p : ℕ × ℕ, (u p.1 * v p.2) *
        (Real.cos ((p.1 : ℝ) * Real.pi * x / L) *
          Real.cos ((p.2 : ℝ) * Real.pi * x / L)) :=
  tsum_mul_tsum_bounded u v _ _ hu hv (fun i => norm_cos_phase_le_one L i x)
    (fun j => norm_cos_phase_le_one L j x)

/-- Product of three absolutely summable cosine series, pointwise, indexed by
`(i, j, ℓ) : ℕ × ℕ × ℕ`. -/
theorem cosineSeries_mul_cosineSeries_mul_cosineSeries (L : ℝ)
    (u v w : ℕ → ℝ) (hu : Summable fun i => ‖u i‖)
    (hv : Summable fun j => ‖v j‖) (hw : Summable fun l => ‖w l‖) (x : ℝ) :
    (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
        (∑' j : ℕ, v j * Real.cos ((j : ℝ) * Real.pi * x / L)) *
        (∑' l : ℕ, w l * Real.cos ((l : ℝ) * Real.pi * x / L)) =
      ∑' t : ℕ × ℕ × ℕ, (u t.1 * (v t.2.1 * w t.2.2)) *
        (Real.cos ((t.1 : ℝ) * Real.pi * x / L) *
          (Real.cos ((t.2.1 : ℝ) * Real.pi * x / L) *
            Real.cos ((t.2.2 : ℝ) * Real.pi * x / L))) := by
  rw [mul_assoc, cosineSeries_mul_cosineSeries L v w hv hw x]
  exact tsum_mul_tsum_bounded u (fun q : ℕ × ℕ => v q.1 * w q.2) _ _ hu
    (hv.mul_norm hw) (fun i => norm_cos_phase_le_one L i x)
    (fun q => norm_cos_phase_mul_le_one L q x)

/-! ### Step 2: interchange with the interval integral -/

/-- One series: termwise integration against a bounded continuous kernel,
with the coefficient pulled out of each integral. -/
theorem hasSum_integral_tsum_mul {ι : Type*} [Countable ι] (a b : ℝ)
    (u : ι → ℝ) (f : ι → ℝ → ℝ) (kernel : ℝ → ℝ) (C : ℝ)
    (hu : Summable fun i => ‖u i‖)
    (hf_cont : ∀ i, Continuous (f i)) (hf : ∀ i x, ‖f i x‖ ≤ 1)
    (hk_cont : Continuous kernel) (hk : ∀ x, ‖kernel x‖ ≤ C) (hC : 0 ≤ C) :
    HasSum (fun i => u i * ∫ x in a..b, f i x * kernel x)
      (∫ x in a..b, (∑' i, u i * f i x) * kernel x) := by
  have h := hasSum_intervalIntegral_boundedPhase a b u f kernel C hu
    hf_cont hf hk_cont hk hC
  simp only [boundedPhaseTerm] at h
  convert h using 1
  · funext i
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    ring
  · congr 1
    funext x
    rw [← tsum_mul_right]

/-- Two series: the product of the separately summed series, integrated
against a bounded continuous kernel, is the product-index sum of the
coefficient products times the kernel integrals. -/
theorem hasSum_integral_tsum_mul_tsum {ι ι' : Type*} [Countable ι]
    [Countable ι'] (a b : ℝ) (u : ι → ℝ) (v : ι' → ℝ)
    (f : ι → ℝ → ℝ) (g : ι' → ℝ → ℝ) (kernel : ℝ → ℝ) (C : ℝ)
    (hu : Summable fun i => ‖u i‖) (hv : Summable fun j => ‖v j‖)
    (hf_cont : ∀ i, Continuous (f i)) (hf : ∀ i x, ‖f i x‖ ≤ 1)
    (hg_cont : ∀ j, Continuous (g j)) (hg : ∀ j x, ‖g j x‖ ≤ 1)
    (hk_cont : Continuous kernel) (hk : ∀ x, ‖kernel x‖ ≤ C) (hC : 0 ≤ C) :
    HasSum (fun p : ι × ι' => u p.1 * v p.2 * ∫ x in a..b, f p.1 x * g p.2 x * kernel x)
      (∫ x in a..b, (∑' i, u i * f i x) * (∑' j, v j * g j x) * kernel x) := by
  have hfg : ∀ (p : ι × ι') (x : ℝ), ‖f p.1 x * g p.2 x‖ ≤ 1 := by
    intro p x
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul (hf p.1 x) (hg p.2 x)
      (norm_nonneg _) (by norm_num)
  have h := hasSum_integral_tsum_mul a b (fun p : ι × ι' => u p.1 * v p.2)
    (fun p x => f p.1 x * g p.2 x) kernel C (hu.mul_norm hv)
    (fun p => (hf_cont p.1).mul (hg_cont p.2)) hfg hk_cont hk hC
  convert h using 2
  funext x
  rw [tsum_mul_tsum_bounded u v (fun i => f i x) (fun j => g j x) hu hv
    (fun i => hf i x) (fun j => hg j x)]


/-! ### Step 3: signed-index reindexing -/

/-- An absolutely summable family weighted by the indicator of a constraint
sums to the constrained sum, i.e. the tsum over the subtype of indices that
satisfy the constraint. -/
theorem hasSum_mul_ite {β : Type*} (c : β → ℝ) (hc : Summable fun b => ‖c b‖)
    (P : β → Prop) [DecidablePred P] :
    HasSum (fun b => c b * (if P b then 1 else 0)) (∑' b : {b // P b}, c b) := by
  have hs : Summable (c ∘ (↑) : {b // P b} → ℝ) := hc.of_norm.subtype P
  have h := (hasSum_subtype_iff_indicator (s := {b | P b}) (f := c)).1 hs.hasSum
  convert h using 1
  · funext b
    by_cases hb : P b <;> simp [hb, Set.indicator]
  · rfl

/-- A single-index sum against the indicator of the integer constraint
`(i : ℤ) = r` picks out the coefficient `u r` when `r ≥ 0` and is empty
otherwise. -/
theorem hasSum_mul_ite_int_eq (u : ℕ → ℝ) (r : ℤ) :
    HasSum (fun i : ℕ => u i * (if (i : ℤ) = r then 1 else 0))
      (if 0 ≤ r then u r.toNat else 0) := by
  by_cases hr : 0 ≤ r
  · simp only [hr, ↓reduceIte]
    convert hasSum_ite_eq r.toNat (u r.toNat) using 1
    funext i
    by_cases hi : i = r.toNat
    · subst hi
      simp [Int.toNat_of_nonneg hr]
    · have : ¬ (i : ℤ) = r := by omega
      simp [hi, this]
  · simp only [hr, ↓reduceIte]
    convert hasSum_zero (α := ℝ) (β := ℕ) using 1
    funext i
    have : ¬ (i : ℤ) = r := by omega
    simp [this]

/-- The pair constraint `i + j = -k` (integer arithmetic) has the single
solution `i = j = k = 0`: it contributes `1_{k=0} u₀ v₀`. -/
theorem hasSum_pair_ite_add_eq_neg (u v : ℕ → ℝ) (k : ℕ) :
    HasSum (fun p : ℕ × ℕ => u p.1 * v p.2 *
        (if (p.1 : ℤ) + p.2 = -(k : ℤ) then 1 else 0))
      (if k = 0 then u 0 * v 0 else 0) := by
  convert hasSum_ite_eq ((0, 0) : ℕ × ℕ) (if k = 0 then u 0 * v 0 else 0)
    using 1
  funext p
  obtain ⟨i, j⟩ := p
  by_cases hp : ((i, j) : ℕ × ℕ) = (0, 0)
  · simp only [Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    by_cases hk : k = 0
    · subst hk
      simp
    · simp [hk]
  · have h : ¬ (i : ℤ) + j = -(k : ℤ) := by
      intro h
      apply hp
      simp only [Prod.mk.injEq]
      omega
    simp [h, hp]

/-- A pair constraint `i + j = r` with a negative integer `r` has no
solutions. -/
theorem hasSum_pair_ite_add_eq_of_neg (u v : ℕ → ℝ) (r : ℤ) (hr : r < 0) :
    HasSum (fun p : ℕ × ℕ => u p.1 * v p.2 *
        (if (p.1 : ℤ) + p.2 = r then 1 else 0)) 0 := by
  convert hasSum_zero (α := ℝ) (β := ℕ × ℕ) using 1
  funext p
  have : ¬ (p.1 : ℤ) + p.2 = r := by omega
  simp [this]

/-- The triple constraint `i + j + ℓ = -k` has the single solution
`i = j = ℓ = k = 0`: it contributes `1_{k=0} u₀ v₀ w₀`. -/
theorem hasSum_triple_ite_add_add_eq_neg (u v w : ℕ → ℝ) (k : ℕ) :
    HasSum (fun t : ℕ × ℕ × ℕ => u t.1 * v t.2.1 * w t.2.2 *
        (if (t.1 : ℤ) + t.2.1 + t.2.2 = -(k : ℤ) then 1 else 0))
      (if k = 0 then u 0 * v 0 * w 0 else 0) := by
  convert hasSum_ite_eq ((0, 0, 0) : ℕ × ℕ × ℕ)
    (if k = 0 then u 0 * v 0 * w 0 else 0) using 1
  funext t
  obtain ⟨i, j, l⟩ := t
  by_cases hp : ((i, j, l) : ℕ × ℕ × ℕ) = (0, 0, 0)
  · simp only [Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl, rfl⟩ := hp
    by_cases hk : k = 0
    · subst hk
      simp
    · simp [hk]
  · have h : ¬ (i : ℤ) + j + l = -(k : ℤ) := by
      intro h
      apply hp
      simp only [Prod.mk.injEq]
      omega
    simp [h, hp]

/-! ### The four product identities, conditional on the kernel integrals

Each theorem takes as hypothesis `hK` the closed-form kernel integral in the
raw product-to-sum indicator form: the coefficient `L/4` or `L/8` times the
signed sum of the indicators of *all* `2^(m-1)` integer constraints produced
by the product-to-sum formulas, including the ones that are empty
(`i + j = -(n+k)`, `i = -(n+k)`) or degenerate (`i + j = -k`,
`i + j + ℓ = -k`).  The conclusion is the product identity, with each
constrained sum `∑_{i-j=r} u_i v_j` read as the tsum over the subtype of
`ℕ × ℕ` (or `ℕ × ℕ × ℕ`) cut out by the integer constraint. -/

theorem norm_sin_phase_le_one (L : ℝ) (n : ℕ) (x : ℝ) :
    ‖Real.sin ((n : ℝ) * Real.pi * x / L)‖ ≤ 1 := by
  simpa only [Real.norm_eq_abs] using
    Real.abs_sin_le_one ((n : ℝ) * Real.pi * x / L)

theorem continuous_cos_phase (L : ℝ) (n : ℕ) :
    Continuous fun x : ℝ => Real.cos ((n : ℝ) * Real.pi * x / L) := by
  fun_prop

theorem continuous_sin_phase (L : ℝ) (n : ℕ) :
    Continuous fun x : ℝ => Real.sin ((n : ℝ) * Real.pi * x / L) := by
  fun_prop

theorem norm_sin_mul_sin_le_one (L : ℝ) (n k : ℕ) (x : ℝ) :
    ‖Real.sin ((n : ℝ) * Real.pi * x / L) *
      Real.sin ((k : ℝ) * Real.pi * x / L)‖ ≤ 1 := by
  rw [norm_mul]
  simpa only [one_mul] using mul_le_mul (norm_sin_phase_le_one L n x)
    (norm_sin_phase_le_one L k x) (norm_nonneg _) (by norm_num)

/-- The three-cosine identity, conditional on the three-cosine kernel
integral. -/
theorem cos_cos_cos_of_kernel (L : ℝ) (u v : ℕ → ℝ)
    (hu : Summable fun i => ‖u i‖) (hv : Summable fun j => ‖v j‖) (k : ℕ)
    (hK : ∀ i j : ℕ, ∫ x in (0 : ℝ)..L,
        Real.cos ((i : ℝ) * Real.pi * x / L) *
          Real.cos ((j : ℝ) * Real.pi * x / L) *
          Real.cos ((k : ℝ) * Real.pi * x / L) =
        L / 4 * ((if (i : ℤ) + j = k then 1 else 0) +
          (if (i : ℤ) + j = -(k : ℤ) then 1 else 0) +
          (if (i : ℤ) - j = k then 1 else 0) +
          (if (i : ℤ) - j = -(k : ℤ) then 1 else 0))) :
    ∫ x in (0 : ℝ)..L,
        (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
          (∑' j : ℕ, v j * Real.cos ((j : ℝ) * Real.pi * x / L)) *
          Real.cos ((k : ℝ) * Real.pi * x / L) =
      L / 4 * ((∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = k}, u p.1.1 * v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = -(k : ℤ)},
            u p.1.1 * v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) + p.2 = k}, u p.1.1 * v p.1.2)) +
        L / 4 * (if k = 0 then u 0 * v 0 else 0) := by
  have h := hasSum_integral_tsum_mul_tsum 0 L u v
    (fun i x => Real.cos ((i : ℝ) * Real.pi * x / L))
    (fun j x => Real.cos ((j : ℝ) * Real.pi * x / L))
    (fun x => Real.cos ((k : ℝ) * Real.pi * x / L)) 1 hu hv
    (continuous_cos_phase L) (norm_cos_phase_le_one L)
    (continuous_cos_phase L) (norm_cos_phase_le_one L)
    (continuous_cos_phase L k) (norm_cos_phase_le_one L k) zero_le_one
  simp only [hK] at h
  have hc : Summable fun p : ℕ × ℕ => ‖u p.1 * v p.2‖ := hu.mul_norm hv
  have h1 := hasSum_mul_ite (fun p : ℕ × ℕ => u p.1 * v p.2) hc
    (fun p => (p.1 : ℤ) - p.2 = k)
  have h2 := hasSum_mul_ite (fun p : ℕ × ℕ => u p.1 * v p.2) hc
    (fun p => (p.1 : ℤ) - p.2 = -(k : ℤ))
  have h3 := hasSum_mul_ite (fun p : ℕ × ℕ => u p.1 * v p.2) hc
    (fun p => (p.1 : ℤ) + p.2 = k)
  have h4 := hasSum_pair_ite_add_eq_neg u v k
  have hR := (((h1.add h2).add h3).mul_left (L / 4)).add (h4.mul_left (L / 4))
  refine h.unique ?_
  convert hR using 1
  funext p
  ring

/-- The two-cosine/two-sine identity, conditional on the two-cosine/two-sine
kernel integral (`n, k ≥ 1`). -/
theorem two_cosines_two_sines_of_kernel (L : ℝ) (u v : ℕ → ℝ)
    (hu : Summable fun i => ‖u i‖) (hv : Summable fun j => ‖v j‖) (n k : ℕ)
    (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hK : ∀ i j : ℕ, ∫ x in (0 : ℝ)..L,
        Real.cos ((i : ℝ) * Real.pi * x / L) *
          Real.cos ((j : ℝ) * Real.pi * x / L) *
          Real.sin ((n : ℝ) * Real.pi * x / L) *
          Real.sin ((k : ℝ) * Real.pi * x / L) =
        L / 8 * ((if (i : ℤ) - j = (n : ℤ) - k then 1 else 0) +
          (if (i : ℤ) - j = -((n : ℤ) - k) then 1 else 0) +
          (if (i : ℤ) + j = (n : ℤ) - k then 1 else 0) +
          (if (i : ℤ) + j = -((n : ℤ) - k) then 1 else 0) -
          (if (i : ℤ) - j = (n : ℤ) + k then 1 else 0) -
          (if (i : ℤ) - j = -((n : ℤ) + k) then 1 else 0) -
          (if (i : ℤ) + j = (n : ℤ) + k then 1 else 0) -
          (if (i : ℤ) + j = -((n : ℤ) + k) then 1 else 0))) :
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
  have h := hasSum_integral_tsum_mul_tsum 0 L u v
    (fun i x => Real.cos ((i : ℝ) * Real.pi * x / L))
    (fun j x => Real.cos ((j : ℝ) * Real.pi * x / L))
    (fun x => Real.sin ((n : ℝ) * Real.pi * x / L) *
      Real.sin ((k : ℝ) * Real.pi * x / L)) 1 hu hv
    (continuous_cos_phase L) (norm_cos_phase_le_one L)
    (continuous_cos_phase L) (norm_cos_phase_le_one L)
    ((continuous_sin_phase L n).mul (continuous_sin_phase L k))
    (norm_sin_mul_sin_le_one L n k) zero_le_one
  have hK' : ∀ i j : ℕ, ∫ x in (0 : ℝ)..L,
      Real.cos ((i : ℝ) * Real.pi * x / L) *
        Real.cos ((j : ℝ) * Real.pi * x / L) *
        (Real.sin ((n : ℝ) * Real.pi * x / L) *
          Real.sin ((k : ℝ) * Real.pi * x / L)) =
      L / 8 * ((if (i : ℤ) - j = (n : ℤ) - k then 1 else 0) +
        (if (i : ℤ) - j = -((n : ℤ) - k) then 1 else 0) +
        (if (i : ℤ) + j = (n : ℤ) - k then 1 else 0) +
        (if (i : ℤ) + j = -((n : ℤ) - k) then 1 else 0) -
        (if (i : ℤ) - j = (n : ℤ) + k then 1 else 0) -
        (if (i : ℤ) - j = -((n : ℤ) + k) then 1 else 0) -
        (if (i : ℤ) + j = (n : ℤ) + k then 1 else 0) -
        (if (i : ℤ) + j = -((n : ℤ) + k) then 1 else 0)) := by
    intro i j
    rw [← hK i j]
    simp only [mul_assoc]
  simp only [hK'] at h
  have hLHS : (∫ x in (0 : ℝ)..L,
        (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
          (∑' j : ℕ, v j * Real.cos ((j : ℝ) * Real.pi * x / L)) *
          Real.sin ((n : ℝ) * Real.pi * x / L) *
          Real.sin ((k : ℝ) * Real.pi * x / L)) =
      ∫ x in (0 : ℝ)..L,
        (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
          (∑' j : ℕ, v j * Real.cos ((j : ℝ) * Real.pi * x / L)) *
          (Real.sin ((n : ℝ) * Real.pi * x / L) *
            Real.sin ((k : ℝ) * Real.pi * x / L)) :=
    intervalIntegral.integral_congr fun x _ => by ring
  rw [hLHS]
  have hc : Summable fun p : ℕ × ℕ => ‖u p.1 * v p.2‖ := hu.mul_norm hv
  have h1 := hasSum_mul_ite (fun p : ℕ × ℕ => u p.1 * v p.2) hc
    (fun p => (p.1 : ℤ) - p.2 = (n : ℤ) - k)
  have h2 := hasSum_mul_ite (fun p : ℕ × ℕ => u p.1 * v p.2) hc
    (fun p => (p.1 : ℤ) - p.2 = -((n : ℤ) - k))
  have h3 := hasSum_mul_ite (fun p : ℕ × ℕ => u p.1 * v p.2) hc
    (fun p => (p.1 : ℤ) + p.2 = (n : ℤ) - k)
  have h4 := hasSum_mul_ite (fun p : ℕ × ℕ => u p.1 * v p.2) hc
    (fun p => (p.1 : ℤ) + p.2 = -((n : ℤ) - k))
  have h5 := hasSum_mul_ite (fun p : ℕ × ℕ => u p.1 * v p.2) hc
    (fun p => (p.1 : ℤ) - p.2 = (n : ℤ) + k)
  have h6 := hasSum_mul_ite (fun p : ℕ × ℕ => u p.1 * v p.2) hc
    (fun p => (p.1 : ℤ) - p.2 = -((n : ℤ) + k))
  have h7 := hasSum_mul_ite (fun p : ℕ × ℕ => u p.1 * v p.2) hc
    (fun p => (p.1 : ℤ) + p.2 = (n : ℤ) + k)
  have h8 := hasSum_pair_ite_add_eq_of_neg u v (-((n : ℤ) + k)) (by omega)
  have hR := ((((((((h1.add h2).add h3).add h4).sub h5).sub h6).sub h7).sub
    h8).mul_left (L / 8))
  refine h.unique ?_
  convert hR using 1
  · funext p
    ring
  · ring

/-- The four-cosine identity, conditional on the four-cosine kernel
integral. -/
theorem cos_cos_cos_cos_of_kernel (L : ℝ) (u v w : ℕ → ℝ)
    (hu : Summable fun i => ‖u i‖) (hv : Summable fun j => ‖v j‖)
    (hw : Summable fun l => ‖w l‖) (k : ℕ)
    (hK : ∀ i j l : ℕ, ∫ x in (0 : ℝ)..L,
        Real.cos ((i : ℝ) * Real.pi * x / L) *
          Real.cos ((j : ℝ) * Real.pi * x / L) *
          Real.cos ((l : ℝ) * Real.pi * x / L) *
          Real.cos ((k : ℝ) * Real.pi * x / L) =
        L / 8 * ((if (i : ℤ) + j + l = k then 1 else 0) +
          (if (i : ℤ) + j + l = -(k : ℤ) then 1 else 0) +
          (if (i : ℤ) + j - l = k then 1 else 0) +
          (if (i : ℤ) + j - l = -(k : ℤ) then 1 else 0) +
          (if (i : ℤ) - j + l = k then 1 else 0) +
          (if (i : ℤ) - j + l = -(k : ℤ) then 1 else 0) +
          (if (i : ℤ) - j - l = k then 1 else 0) +
          (if (i : ℤ) - j - l = -(k : ℤ) then 1 else 0))) :
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
  have h := hasSum_integral_tsum_mul_tsum 0 L u (fun q : ℕ × ℕ => v q.1 * w q.2)
    (fun i x => Real.cos ((i : ℝ) * Real.pi * x / L))
    (fun q x => Real.cos ((q.1 : ℝ) * Real.pi * x / L) *
      Real.cos ((q.2 : ℝ) * Real.pi * x / L))
    (fun x => Real.cos ((k : ℝ) * Real.pi * x / L)) 1 hu (hv.mul_norm hw)
    (continuous_cos_phase L) (norm_cos_phase_le_one L)
    (fun q => (continuous_cos_phase L q.1).mul (continuous_cos_phase L q.2))
    (norm_cos_phase_mul_le_one L)
    (continuous_cos_phase L k) (norm_cos_phase_le_one L k) zero_le_one
  have hK' : ∀ (i : ℕ) (q : ℕ × ℕ), ∫ x in (0 : ℝ)..L,
      Real.cos ((i : ℝ) * Real.pi * x / L) *
        (Real.cos ((q.1 : ℝ) * Real.pi * x / L) *
          Real.cos ((q.2 : ℝ) * Real.pi * x / L)) *
        Real.cos ((k : ℝ) * Real.pi * x / L) =
      L / 8 * ((if (i : ℤ) + q.1 + q.2 = k then 1 else 0) +
        (if (i : ℤ) + q.1 + q.2 = -(k : ℤ) then 1 else 0) +
        (if (i : ℤ) + q.1 - q.2 = k then 1 else 0) +
        (if (i : ℤ) + q.1 - q.2 = -(k : ℤ) then 1 else 0) +
        (if (i : ℤ) - q.1 + q.2 = k then 1 else 0) +
        (if (i : ℤ) - q.1 + q.2 = -(k : ℤ) then 1 else 0) +
        (if (i : ℤ) - q.1 - q.2 = k then 1 else 0) +
        (if (i : ℤ) - q.1 - q.2 = -(k : ℤ) then 1 else 0)) := by
    intro i q
    rw [← hK i q.1 q.2]
    simp only [mul_assoc]
  simp only [hK'] at h
  have hLHS : (∫ x in (0 : ℝ)..L,
        (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
          (∑' j : ℕ, v j * Real.cos ((j : ℝ) * Real.pi * x / L)) *
          (∑' l : ℕ, w l * Real.cos ((l : ℝ) * Real.pi * x / L)) *
          Real.cos ((k : ℝ) * Real.pi * x / L)) =
      ∫ x in (0 : ℝ)..L,
        (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
          (∑' q : ℕ × ℕ, (v q.1 * w q.2) *
            (Real.cos ((q.1 : ℝ) * Real.pi * x / L) *
              Real.cos ((q.2 : ℝ) * Real.pi * x / L))) *
          Real.cos ((k : ℝ) * Real.pi * x / L) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [mul_assoc (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)),
      cosineSeries_mul_cosineSeries L v w hv hw x]
  rw [hLHS]
  have hc : Summable fun t : ℕ × ℕ × ℕ => ‖u t.1 * v t.2.1 * w t.2.2‖ := by
    simpa only [mul_assoc] using hu.mul_norm (hv.mul_norm hw)
  have h1 := hasSum_mul_ite (fun t : ℕ × ℕ × ℕ => u t.1 * v t.2.1 * w t.2.2)
    hc (fun t => (t.1 : ℤ) + t.2.1 + t.2.2 = k)
  have h2 := hasSum_mul_ite (fun t : ℕ × ℕ × ℕ => u t.1 * v t.2.1 * w t.2.2)
    hc (fun t => (t.1 : ℤ) + t.2.1 - t.2.2 = k)
  have h3 := hasSum_mul_ite (fun t : ℕ × ℕ × ℕ => u t.1 * v t.2.1 * w t.2.2)
    hc (fun t => (t.1 : ℤ) + t.2.1 - t.2.2 = -(k : ℤ))
  have h4 := hasSum_mul_ite (fun t : ℕ × ℕ × ℕ => u t.1 * v t.2.1 * w t.2.2)
    hc (fun t => (t.1 : ℤ) - t.2.1 + t.2.2 = k)
  have h5 := hasSum_mul_ite (fun t : ℕ × ℕ × ℕ => u t.1 * v t.2.1 * w t.2.2)
    hc (fun t => (t.1 : ℤ) - t.2.1 + t.2.2 = -(k : ℤ))
  have h6 := hasSum_mul_ite (fun t : ℕ × ℕ × ℕ => u t.1 * v t.2.1 * w t.2.2)
    hc (fun t => (t.1 : ℤ) - t.2.1 - t.2.2 = k)
  have h7 := hasSum_mul_ite (fun t : ℕ × ℕ × ℕ => u t.1 * v t.2.1 * w t.2.2)
    hc (fun t => (t.1 : ℤ) - t.2.1 - t.2.2 = -(k : ℤ))
  have h8 := hasSum_triple_ite_add_add_eq_neg u v w k
  have hR := (((((((h1.add h2).add h3).add h4).add h5).add h6).add
    h7).mul_left (L / 8)).add (h8.mul_left (L / 8))
  refine h.unique ?_
  convert hR using 1
  funext t
  ring

/-- The one-cosine/two-sine identity, conditional on the one-cosine/two-sine
kernel integral (`n, k ≥ 1`).  Here `u_{|n-k|}` is
`u (Int.natAbs (n - k))` with the difference taken in `ℤ`, and `δ_{nk} u₀` is
`if n = k then u 0 else 0`. -/
theorem cosine_sine_sine_of_kernel (L : ℝ) (u : ℕ → ℝ)
    (hu : Summable fun i => ‖u i‖) (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hK : ∀ i : ℕ, ∫ x in (0 : ℝ)..L,
        Real.cos ((i : ℝ) * Real.pi * x / L) *
          Real.sin ((n : ℝ) * Real.pi * x / L) *
          Real.sin ((k : ℝ) * Real.pi * x / L) =
        L / 4 * ((if (i : ℤ) = (n : ℤ) - k then 1 else 0) +
          (if (i : ℤ) = -((n : ℤ) - k) then 1 else 0) -
          (if (i : ℤ) = (n : ℤ) + k then 1 else 0) -
          (if (i : ℤ) = -((n : ℤ) + k) then 1 else 0))) :
    ∫ x in (0 : ℝ)..L,
        (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
          Real.sin ((n : ℝ) * Real.pi * x / L) *
          Real.sin ((k : ℝ) * Real.pi * x / L) =
      L / 4 * (u (Int.natAbs ((n : ℤ) - k)) - u (n + k) +
        (if n = k then u 0 else 0)) := by
  have h := hasSum_integral_tsum_mul 0 L u
    (fun i x => Real.cos ((i : ℝ) * Real.pi * x / L))
    (fun x => Real.sin ((n : ℝ) * Real.pi * x / L) *
      Real.sin ((k : ℝ) * Real.pi * x / L)) 1 hu
    (continuous_cos_phase L) (norm_cos_phase_le_one L)
    ((continuous_sin_phase L n).mul (continuous_sin_phase L k))
    (norm_sin_mul_sin_le_one L n k) zero_le_one
  have hK' : ∀ i : ℕ, ∫ x in (0 : ℝ)..L,
      Real.cos ((i : ℝ) * Real.pi * x / L) *
        (Real.sin ((n : ℝ) * Real.pi * x / L) *
          Real.sin ((k : ℝ) * Real.pi * x / L)) =
      L / 4 * ((if (i : ℤ) = (n : ℤ) - k then 1 else 0) +
        (if (i : ℤ) = -((n : ℤ) - k) then 1 else 0) -
        (if (i : ℤ) = (n : ℤ) + k then 1 else 0) -
        (if (i : ℤ) = -((n : ℤ) + k) then 1 else 0)) := by
    intro i
    rw [← hK i]
    simp only [mul_assoc]
  simp only [hK'] at h
  have hLHS : (∫ x in (0 : ℝ)..L,
        (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
          Real.sin ((n : ℝ) * Real.pi * x / L) *
          Real.sin ((k : ℝ) * Real.pi * x / L)) =
      ∫ x in (0 : ℝ)..L,
        (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
          (Real.sin ((n : ℝ) * Real.pi * x / L) *
            Real.sin ((k : ℝ) * Real.pi * x / L)) :=
    intervalIntegral.integral_congr fun x _ => by ring
  rw [hLHS]
  have h1 := hasSum_mul_ite_int_eq u ((n : ℤ) - k)
  have h2 := hasSum_mul_ite_int_eq u (-((n : ℤ) - k))
  have h3 := hasSum_mul_ite_int_eq u ((n : ℤ) + k)
  have h4 := hasSum_mul_ite_int_eq u (-((n : ℤ) + k))
  have hR := (((h1.add h2).sub h3).sub h4).mul_left (L / 4)
  have hval := h.unique (by convert hR using 1; funext i; ring)
  rw [hval]
  have e3 : (0 : ℤ) ≤ (n : ℤ) + k := by omega
  have e3' : ((n : ℤ) + k).toNat = n + k := by omega
  have e4 : ¬ (0 : ℤ) ≤ -((n : ℤ) + k) := by omega
  simp only [e3, e3', e4, ↓reduceIte]
  rcases lt_trichotomy n k with hnk | hnk | hnk
  · have a1 : ¬ (0 : ℤ) ≤ (n : ℤ) - k := by omega
    have a2 : (0 : ℤ) ≤ -((n : ℤ) - k) := by omega
    have a3 : (-((n : ℤ) - k)).toNat = Int.natAbs ((n : ℤ) - k) := by omega
    have a4 : n ≠ k := by omega
    simp only [a1, a2, a3, a4, ↓reduceIte]
    ring
  · subst hnk
    have a1 : (n : ℤ) - n = 0 := sub_self _
    have a2 : (0 : ℤ).toNat = 0 := rfl
    have a3 : Int.natAbs 0 = 0 := rfl
    simp only [a1, a2, a3, neg_zero, le_refl, ↓reduceIte]
    ring
  · have a1 : (0 : ℤ) ≤ (n : ℤ) - k := by omega
    have a2 : ¬ (0 : ℤ) ≤ -((n : ℤ) - k) := by omega
    have a3 : ((n : ℤ) - k).toNat = Int.natAbs ((n : ℤ) - k) := by omega
    have a4 : n ≠ k := by omega
    simp only [a1, a2, a3, a4, ↓reduceIte]
    ring

/-- `ℓ¹(ℕ₀)` membership, as Mathlib's `lp` at exponent `1`, gives the
absolute summability hypothesis used throughout this file. -/
theorem summable_norm_of_lp_one (u : lp (fun _ : ℕ => ℝ) 1) :
    Summable fun i => ‖u i‖ := by
  simpa using (lp.memℓp u).summable (by norm_num)

end

end NeumannCosine.Series.Products
