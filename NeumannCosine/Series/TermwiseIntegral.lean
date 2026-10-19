module
/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/

public import NeumannCosine.Basic

@[expose] public section

/-!
# Termwise integration of absolutely summable cosine series

Let `c` be an absolutely summable coefficient family and let each phase have
norm at most one. Then the series `∑ c_i φ_i(x) K(x)` can be integrated term by
term over an interval against a bounded continuous kernel `K`.

We apply this to one, two and three Neumann cosine series. The index sets are
`ℕ`, `ℕ × ℕ` and `(ℕ × ℕ) × ℕ`. No reindexing of the product index is done here.
-/

namespace NeumannCosine.Series.TermwiseIntegral

open MeasureTheory Set
open scoped Interval

noncomputable section

/-- A coefficient, a uniformly bounded phase, and a bounded kernel. -/
def boundedPhaseTerm {ι : Type*} (c : ι → ℝ) (phase : ι → ℝ → ℝ)
    (kernel : ℝ → ℝ) (i : ι) (x : ℝ) : ℝ :=
  c i * phase i x * kernel x

/-- Absolute coefficient summability controls the pointwise series whenever
the phase has norm at most one and the kernel has a uniform bound. -/
theorem summable_boundedPhaseTerm {ι : Type*} (c : ι → ℝ)
    (phase : ι → ℝ → ℝ) (kernel : ℝ → ℝ) (C : ℝ)
    (hc : Summable fun i => ‖c i‖)
    (hphase : ∀ i x, ‖phase i x‖ ≤ 1)
    (hkernel : ∀ x, ‖kernel x‖ ≤ C) (_hC : 0 ≤ C) (x : ℝ) :
    Summable fun i => boundedPhaseTerm c phase kernel i x := by
  apply (hc.mul_right C).of_norm_bounded
  intro i
  rw [boundedPhaseTerm, norm_mul, norm_mul]
  calc
    ‖c i‖ * ‖phase i x‖ * ‖kernel x‖ ≤
        (‖c i‖ * 1) * ‖kernel x‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hphase i x) (norm_nonneg _))
        (norm_nonneg _)
    _ ≤ (‖c i‖ * 1) * C :=
      mul_le_mul_of_nonneg_left (hkernel x)
        (mul_nonneg (norm_nonneg _) (by norm_num))
    _ = ‖c i‖ * C := by ring

/-- Dominated convergence: absolute summability of the coefficients gives
termwise interval integration against a bounded continuous kernel.

The conclusion is a `HasSum`. It gives both summability and the value of the
sum, not only an equality of `tsum` values. -/
theorem hasSum_intervalIntegral_boundedPhase {ι : Type*} [Countable ι]
    (a b : ℝ) (c : ι → ℝ) (phase : ι → ℝ → ℝ)
    (kernel : ℝ → ℝ) (C : ℝ)
    (hc : Summable fun i => ‖c i‖)
    (hphase_cont : ∀ i, Continuous (phase i))
    (hphase : ∀ i x, ‖phase i x‖ ≤ 1)
    (hkernel_cont : Continuous kernel)
    (hkernel : ∀ x, ‖kernel x‖ ≤ C) (hC : 0 ≤ C) :
    HasSum
      (fun i => ∫ x in a..b, boundedPhaseTerm c phase kernel i x)
      (∫ x in a..b, ∑' i, boundedPhaseTerm c phase kernel i x) := by
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun i (_x : ℝ) => ‖c i‖ * C)
  · intro i
    exact ((continuous_const.mul (hphase_cont i)).mul
      hkernel_cont).aestronglyMeasurable
  · intro i
    filter_upwards with x
    intro _hx
    rw [boundedPhaseTerm, norm_mul, norm_mul]
    calc
      ‖c i‖ * ‖phase i x‖ * ‖kernel x‖ ≤
          (‖c i‖ * 1) * ‖kernel x‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hphase i x) (norm_nonneg _))
          (norm_nonneg _)
      _ ≤ (‖c i‖ * 1) * C :=
        mul_le_mul_of_nonneg_left (hkernel x)
          (mul_nonneg (norm_nonneg _) (by norm_num))
      _ = ‖c i‖ * C := by ring
  · filter_upwards with x
    intro _hx
    exact hc.mul_right C
  · exact intervalIntegrable_const
  · filter_upwards with x
    intro _hx
    exact (summable_boundedPhaseTerm c phase kernel C hc hphase
      hkernel hC x).hasSum

/-- Termwise integration of one cosine series against a bounded continuous
kernel. The kernel may be, for example, a product of two sine modes. -/
theorem hasSum_intervalIntegral_cosine (a b L : ℝ) (u : ℕ → ℝ)
    (kernel : ℝ → ℝ) (C : ℝ)
    (hu : Summable fun n => ‖u n‖)
    (hkernel_cont : Continuous kernel)
    (hkernel : ∀ x, ‖kernel x‖ ≤ C) (hC : 0 ≤ C) :
    HasSum
      (fun n => ∫ x in a..b,
        u n * mode L n x * kernel x)
      (∫ x in a..b, ∑' n,
        u n * mode L n x * kernel x) := by
  simpa only [boundedPhaseTerm] using
    hasSum_intervalIntegral_boundedPhase a b u (mode L)
      kernel C hu (continuous_mode L)
      (norm_mode_le_one L) hkernel_cont hkernel hC

/-- Product coefficients of two absolutely summable sequences are absolutely
summable on the product index. -/
theorem summable_norm_pairCoefficient (u v : ℕ → ℝ)
    (hu : Summable fun i => ‖u i‖)
    (hv : Summable fun j => ‖v j‖) :
    Summable fun p : ℕ × ℕ => ‖u p.1 * v p.2‖ :=
  hu.mul_norm hv

/-- Product of two Neumann modes, indexed by `ℕ × ℕ`. -/
def pairMode (L : ℝ) (p : ℕ × ℕ) (x : ℝ) : ℝ :=
  mode L p.1 x * mode L p.2 x

theorem continuous_pairMode (L : ℝ) (p : ℕ × ℕ) :
    Continuous (pairMode L p) :=
  (continuous_mode L p.1).mul (continuous_mode L p.2)

theorem norm_pairMode_le_one (L : ℝ) (p : ℕ × ℕ) (x : ℝ) :
    ‖pairMode L p x‖ ≤ 1 := by
  rw [pairMode, norm_mul]
  simpa only [one_mul] using mul_le_mul
    (norm_mode_le_one L p.1 x)
    (norm_mode_le_one L p.2 x)
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

/-- Termwise integration of the product of two cosine series, indexed by
`ℕ × ℕ`. Collecting terms by signed index is done elsewhere. -/
theorem hasSum_intervalIntegral_cosinePair (a b L : ℝ)
    (u v : ℕ → ℝ) (kernel : ℝ → ℝ) (C : ℝ)
    (hu : Summable fun i => ‖u i‖)
    (hv : Summable fun j => ‖v j‖)
    (hkernel_cont : Continuous kernel)
    (hkernel : ∀ x, ‖kernel x‖ ≤ C) (hC : 0 ≤ C) :
    HasSum
      (fun p : ℕ × ℕ => ∫ x in a..b,
        (u p.1 * v p.2) * pairMode L p x * kernel x)
      (∫ x in a..b, ∑' p : ℕ × ℕ,
        (u p.1 * v p.2) * pairMode L p x * kernel x) := by
  simpa only [boundedPhaseTerm] using
    hasSum_intervalIntegral_boundedPhase a b
      (fun p : ℕ × ℕ => u p.1 * v p.2) (pairMode L)
      kernel C (summable_norm_pairCoefficient u v hu hv)
      (continuous_pairMode L) (norm_pairMode_le_one L)
      hkernel_cont hkernel hC

/-- Index set for a product of three series. -/
abbrev TripleIndex := (ℕ × ℕ) × ℕ

def tripleCoefficient (u v w : ℕ → ℝ) (p : TripleIndex) : ℝ :=
  u p.1.1 * v p.1.2 * w p.2

theorem summable_norm_tripleCoefficient (u v w : ℕ → ℝ)
    (hu : Summable fun i => ‖u i‖)
    (hv : Summable fun j => ‖v j‖)
    (hw : Summable fun l => ‖w l‖) :
    Summable fun p : TripleIndex => ‖tripleCoefficient u v w p‖ := by
  have huv : Summable fun p : ℕ × ℕ => ‖u p.1 * v p.2‖ := hu.mul_norm hv
  simpa only [tripleCoefficient, mul_assoc] using huv.mul_norm hw

def tripleMode (L : ℝ) (p : TripleIndex) (x : ℝ) : ℝ :=
  pairMode L p.1 x * mode L p.2 x

theorem continuous_tripleMode (L : ℝ) (p : TripleIndex) :
    Continuous (tripleMode L p) :=
  (continuous_pairMode L p.1).mul (continuous_mode L p.2)

theorem norm_tripleMode_le_one (L : ℝ) (p : TripleIndex) (x : ℝ) :
    ‖tripleMode L p x‖ ≤ 1 := by
  rw [tripleMode, norm_mul]
  simpa only [one_mul] using mul_le_mul
    (norm_pairMode_le_one L p.1 x)
    (norm_mode_le_one L p.2 x)
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

/-- Termwise integration of the product of three cosine series, indexed by
`(ℕ × ℕ) × ℕ`. -/
theorem hasSum_intervalIntegral_cosineTriple (a b L : ℝ)
    (u v w : ℕ → ℝ) (kernel : ℝ → ℝ) (C : ℝ)
    (hu : Summable fun i => ‖u i‖)
    (hv : Summable fun j => ‖v j‖)
    (hw : Summable fun l => ‖w l‖)
    (hkernel_cont : Continuous kernel)
    (hkernel : ∀ x, ‖kernel x‖ ≤ C) (hC : 0 ≤ C) :
    HasSum
      (fun p : TripleIndex => ∫ x in a..b,
        tripleCoefficient u v w p * tripleMode L p x * kernel x)
      (∫ x in a..b, ∑' p : TripleIndex,
        tripleCoefficient u v w p * tripleMode L p x * kernel x) := by
  simpa only [boundedPhaseTerm] using
    hasSum_intervalIntegral_boundedPhase a b
      (tripleCoefficient u v w) (tripleMode L)
      kernel C (summable_norm_tripleCoefficient u v w hu hv hw)
      (continuous_tripleMode L) (norm_tripleMode_le_one L)
      hkernel_cont hkernel hC

end

end NeumannCosine.Series.TermwiseIntegral
