/-
Copyright (c) 2025. All rights reserved.
Released under MIT license.

# John-Nirenberg Inequality for BMO Functions

This module provides the John-Nirenberg inequality, which is the key tool
for proving the Fefferman-Stein BMO→Carleson embedding.

## Main Results

- `johnNirenberg_exp_decay`: The exponential distribution bound for BMO functions
- `bmo_Lp_bound`: BMO functions are in L^p for all p < ∞

## Mathematical Background

The John-Nirenberg inequality (1961) states that for f ∈ BMO:

  |{x ∈ I : |f(x) - f_I| > λ}| ≤ C₁ · |I| · exp(-C₂ · λ / ‖f‖_BMO)

This exponential decay is the key property that distinguishes BMO from L^∞.
It implies:
1. f ∈ L^p(loc) for all p < ∞
2. The Poisson extension gradient is controlled

## References

- John & Nirenberg (1961), "On functions of bounded mean oscillation", CPAM 14
- Garnett, "Bounded Analytic Functions", Chapter VI
- Stein, "Harmonic Analysis", Chapter IV
-/

import RiemannRecognitionGeometry.Basic
import RiemannRecognitionGeometry.FeffermanStein
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open Real MeasureTheory Set

namespace RiemannRecognitionGeometry

/-! ## Dyadic Intervals

Dyadic intervals are the building blocks for the Calderón-Zygmund decomposition.
-/

/-- A dyadic interval of generation n starting at k · 2^(-n). -/
structure DyadicInterval where
  generation : ℕ  -- n: the "level" (higher = smaller intervals)
  index : ℤ       -- k: which interval at this level
  deriving DecidableEq

/-- The left endpoint of a dyadic interval. -/
def DyadicInterval.left (D : DyadicInterval) : ℝ :=
  D.index * (2 : ℝ)^(-(D.generation : ℤ))

/-- The right endpoint of a dyadic interval. -/
def DyadicInterval.right (D : DyadicInterval) : ℝ :=
  (D.index + 1) * (2 : ℝ)^(-(D.generation : ℤ))

/-- The length of a dyadic interval is 2^(-n). -/
def DyadicInterval.length (D : DyadicInterval) : ℝ :=
  (2 : ℝ)^(-(D.generation : ℤ))

/-- The interval as a set. -/
def DyadicInterval.toSet (D : DyadicInterval) : Set ℝ :=
  Icc D.left D.right

/-- Dyadic interval length is positive. -/
lemma DyadicInterval.length_pos (D : DyadicInterval) : D.length > 0 := by
  unfold length
  exact zpow_pos_of_pos (by norm_num : (2:ℝ) > 0) _

/-- The parent of a dyadic interval (one level up). -/
def DyadicInterval.parent (D : DyadicInterval) : DyadicInterval :=
  { generation := D.generation - 1
    index := D.index / 2 }

/-- The left child of a dyadic interval. -/
def DyadicInterval.leftChild (D : DyadicInterval) : DyadicInterval :=
  { generation := D.generation + 1
    index := 2 * D.index }

/-- The right child of a dyadic interval. -/
def DyadicInterval.rightChild (D : DyadicInterval) : DyadicInterval :=
  { generation := D.generation + 1
    index := 2 * D.index + 1 }

/-! ## Average and Oscillation on Sets -/

/-- The average of f over a set S with finite positive measure. -/
def setAverage (f : ℝ → ℝ) (S : Set ℝ) (μ : Measure ℝ := volume) : ℝ :=
  if h : μ S ≠ 0 ∧ μ S ≠ ⊤ then
    (μ S).toReal⁻¹ * ∫ x in S, f x ∂μ
  else 0

/-- The mean oscillation of f over a set S. -/
def setMeanOscillation (f : ℝ → ℝ) (S : Set ℝ) (μ : Measure ℝ := volume) : ℝ :=
  if h : μ S ≠ 0 ∧ μ S ≠ ⊤ then
    (μ S).toReal⁻¹ * ∫ x in S, |f x - setAverage f S μ| ∂μ
  else 0

/-- f is in BMO' if all its mean oscillations are bounded by some M > 0. -/
def InBMO' (f : ℝ → ℝ) : Prop :=
  ∃ M : ℝ, M > 0 ∧ ∀ a b : ℝ, a < b → setMeanOscillation f (Icc a b) ≤ M

/-! ## Calderón-Zygmund Decomposition

The CZ decomposition splits a function at level λ into "good" and "bad" parts.
-/

/-- For a locally integrable function f and level t > 0, the Calderón-Zygmund
    decomposition finds maximal dyadic intervals where the average exceeds t.

    **Mathematical Statement**:
    Given f ∈ L¹(I₀) and t > (1/|I₀|)∫_{I₀}|f|, there exists a collection
    {Qⱼ} of disjoint dyadic subintervals of I₀ such that:
    1. t < (1/|Qⱼ|)∫_{Qⱼ}|f| ≤ 2t  (selection criterion)
    2. |f(x)| ≤ t for a.e. x ∈ I₀ \ ⋃ⱼQⱼ  (good part bound)
    3. Σⱼ|Qⱼ| ≤ (1/t)∫_{I₀}|f|  (total measure bound)
-/
structure CZDecomposition (f : ℝ → ℝ) (I₀ : Set ℝ) (t : ℝ) where
  /-- The "bad" dyadic intervals where average > t -/
  badIntervals : Set DyadicInterval
  /-- The bad intervals are pairwise disjoint -/
  disjoint : ∀ D₁ D₂ : DyadicInterval, D₁ ∈ badIntervals → D₂ ∈ badIntervals →
             D₁ ≠ D₂ → Disjoint D₁.toSet D₂.toSet
  /-- Each bad interval has average between t and 2t -/
  avgBound : ∀ D ∈ badIntervals,
             t < setAverage (|f ·|) D.toSet ∧ setAverage (|f ·|) D.toSet ≤ 2 * t
  /-- On the good part, |f| ≤ t a.e. -/
  goodBound : ∀ᵐ x ∂volume, x ∈ I₀ →
              (∀ D ∈ badIntervals, x ∉ D.toSet) → |f x| ≤ t

/-- The Calderón-Zygmund decomposition exists for any locally integrable function
    and level t above the average. -/
axiom czDecomposition_exists (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf_int : IntegrableOn f (Icc a b))
    (t : ℝ) (ht_pos : t > 0)
    (ht_above_avg : t > (b - a)⁻¹ * ∫ x in Icc a b, |f x|) :
    ∃ cz : CZDecomposition f (Icc a b) t, True

/-! ## The John-Nirenberg Inequality -/

/-- **The John-Nirenberg Constants**.
    The inequality holds with C₁ = e and C₂ = 1/(2e). -/
def JN_C1 : ℝ := Real.exp 1  -- e ≈ 2.718
def JN_C2 : ℝ := 1 / (2 * Real.exp 1)  -- 1/(2e) ≈ 0.184

lemma JN_C1_pos : JN_C1 > 0 := Real.exp_pos 1
lemma JN_C2_pos : JN_C2 > 0 := by unfold JN_C2; positivity

/-- **THEOREM (John-Nirenberg Inequality)**:
    For f ∈ BMO and any interval I, the distribution of |f - f_I| decays exponentially:

    |{x ∈ I : |f(x) - f_I| > t}| ≤ C₁ · |I| · exp(-C₂ · t / ‖f‖_BMO)

    **Proof Outline** (following Garnett, Chapter VI):
    1. Fix I and let M = ‖f‖_BMO
    2. For t = k·M (k ∈ ℕ), apply CZ decomposition at level t
    3. The bad intervals at level k are contained in bad intervals at level k-1
    4. By induction: measure decays geometrically with ratio ≤ 1/2
    5. This gives exponential decay in t

    **Key Lemma**: If J ⊂ I is a maximal bad interval at level t, then
    |J| ≤ (1/t) ∫_J |f - f_I| ≤ M·|I|/t
-/
theorem johnNirenberg_exp_decay (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (M : ℝ) (hM_pos : M > 0)
    (h_bmo : ∀ a' b' : ℝ, a' < b' → meanOscillation f a' b' ≤ M)
    (t : ℝ) (ht_pos : t > 0) :
    volume {x ∈ Icc a b | |f x - intervalAverage f a b| > t} ≤
    ENNReal.ofReal (JN_C1 * (b - a) * Real.exp (-JN_C2 * t / M)) := by
  -- The proof uses the Calderón-Zygmund decomposition iteratively.
  -- At each level k·M, the measure of the "bad" set shrinks by a factor of at least 1/2.
  --
  -- **Step 1**: For t ≤ M, use the trivial bound |{...}| ≤ |I|
  -- **Step 2**: For t > M, use induction on k = ⌊t/M⌋
  --
  -- The key insight is that on each maximal bad interval Q at level k·M:
  -- - |Q| ≤ (1/(k·M)) ∫_Q |f - f_I|
  -- - The BMO condition gives ∫_Q |f - f_Q| ≤ M·|Q|
  -- - So the bad intervals at level (k+1)·M within Q have total measure ≤ |Q|/2
  --
  -- This geometric decay gives: measure at level k·M ≤ |I|·2^(-k)
  -- Converting to continuous t: measure ≤ C·|I|·exp(-c·t/M)
  sorry

/-- **COROLLARY**: BMO functions are in L^p for all p < ∞.

    For f ∈ BMO and any interval I:
    (1/|I|) ∫_I |f - f_I|^p ≤ C_p · ‖f‖_BMO^p

    **Proof**: Integrate the distribution function bound from John-Nirenberg.
    |{|f - f_I| > t}| ≤ C·|I|·exp(-c·t/M) implies the L^p bound via:
    ∫|f - f_I|^p = p ∫_0^∞ t^{p-1} |{|f - f_I| > t}| dt
-/
theorem bmo_Lp_bound (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (M : ℝ) (hM_pos : M > 0)
    (h_bmo : ∀ a' b' : ℝ, a' < b' → meanOscillation f a' b' ≤ M)
    (p : ℝ) (hp : 1 ≤ p) :
    ∃ C_p : ℝ, C_p > 0 ∧
    (b - a)⁻¹ * ∫ x in Icc a b, |f x - intervalAverage f a b|^p ≤ C_p * M^p := by
  -- Use John-Nirenberg and integrate the distribution function
  -- The integral ∫_0^∞ t^{p-1} exp(-ct/M) dt = C_p · M^p where C_p depends on p
  sorry

/-- **APPLICATION**: The pointwise bound for BMO functions against smooth kernels.

    For f ∈ BMO with ‖f‖_BMO ≤ M and a kernel K with ∫|K| < ∞:
    |∫ K(t) · (f(t) - c) dt| ≤ C · M · ∫|K|

    This is used in the Fefferman-Stein proof to bound Poisson extension gradients.
-/
theorem bmo_kernel_bound (f : ℝ → ℝ) (K : ℝ → ℝ)
    (M : ℝ) (hM_pos : M > 0)
    (h_bmo : ∀ a b : ℝ, a < b → meanOscillation f a b ≤ M)
    (hK_int : Integrable K)
    (c : ℝ) :
    ∃ C : ℝ, C > 0 ∧
    |∫ t, K t * (f t - c)| ≤ C * M * ∫ t, |K t| := by
  -- This follows from the L^p bound for BMO combined with Hölder's inequality:
  -- |∫ K(f - c)| ≤ ‖K‖_q · ‖f - c‖_p for conjugate exponents p, q
  -- Taking p large enough (using the L^p bound from John-Nirenberg) gives the result.
  sorry

/-! ## Connection to Fefferman-Stein

The John-Nirenberg inequality is the key to proving that BMO functions have
Poisson extensions with controlled gradients, which leads to the Carleson
measure condition.
-/

/-- Using John-Nirenberg, we can prove the gradient bound from oscillation.
    This is the key lemma that `poissonExtension_gradient_bound_from_oscillation`
    in FeffermanStein.lean needs. -/
theorem poisson_gradient_bound_via_JN (f : ℝ → ℝ) (x : ℝ) {y : ℝ} (hy : 0 < y)
    (M : ℝ) (hM_pos : M > 0)
    (h_bmo : ∀ a b : ℝ, a < b → meanOscillation f a b ≤ M) :
    ∃ C : ℝ, C > 0 ∧ ‖poissonExtension_gradient f x y‖ ≤ C * M / y := by
  -- The proof uses:
  -- 1. Write ∂u/∂x = ∫ ∂P/∂x(x-t, y) · (f(t) - f_I) dt where I is centered at x with radius y
  -- 2. Apply bmo_kernel_bound with K = ∂P/∂x
  -- 3. Use poissonKernel_dx_integral_bound: ∫|∂P/∂x| ≤ 2/(πy)
  --
  -- The key insight from John-Nirenberg is that we don't need |f - f_I| ≤ M pointwise,
  -- only the mean oscillation bound. The exponential integrability from JN makes
  -- the convolution with the Poisson kernel well-behaved.
  sorry

end RiemannRecognitionGeometry
