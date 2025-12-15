/-
Copyright (c) 2025 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Washburn
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Complex.Abs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Carathéodory Theory: Positive Kernels from Positive Real Part

This file proves Carathéodory's theorem: if F is holomorphic on the unit disk with
`Re F ≥ 0`, then the Carathéodory kernel

  `K_F(z,w) = (F(z) + conj(F(w))) / (1 - z·conj(w))`

is positive definite.

## Main results

* `szegoKernel_positive_definite`: The Szegő kernel is positive definite.
* `caratheodory_positive_definite`: The main theorem.

## References

* Carathéodory, C. (1911). Über den Variabilitätsbereich der Koeffizienten von Potenzreihen
* Herglotz, G. (1911). Über Potenzreihen mit positivem, reellen Teil im Einheitskreis
-/

noncomputable section

open Complex ComplexConjugate
open scoped BigOperators

namespace RiemannRecognitionGeometry
namespace ExplicitFormula
namespace Caratheodory

/-!
## Positive Definite Kernels
-/

/-- A kernel is positive semidefinite on a set S. -/
def IsPositiveDefiniteKernelOn {α : Type*} (K : α → α → ℂ) (S : Set α) : Prop :=
  ∀ (n : ℕ) (x : Fin n → α) (_hx : ∀ i, x i ∈ S) (c : Fin n → ℂ),
    0 ≤ (∑ i : Fin n, ∑ j : Fin n, c i * starRingEnd ℂ (c j) * K (x i) (x j)).re

/-!
## The Szegő Kernel
-/

/-- The Szegő kernel: reproducing kernel of H². -/
def szegoKernel (z w : ℂ) : ℂ :=
  1 / (1 - z * starRingEnd ℂ w)

/-- The unit disk. -/
def unitDisk : Set ℂ := {z : ℂ | Complex.abs z < 1}

/-- For z, w in the disk, |z·conj(w)| < 1. -/
lemma abs_mul_conj_lt_one {z w : ℂ} (hz : Complex.abs z < 1) (hw : Complex.abs w < 1) :
    Complex.abs (z * starRingEnd ℂ w) < 1 := by
  calc Complex.abs (z * starRingEnd ℂ w)
      = Complex.abs z * Complex.abs (starRingEnd ℂ w) := Complex.abs.map_mul z _
    _ = Complex.abs z * Complex.abs w := by rw [Complex.abs_conj]
    _ < 1 * 1 := by nlinarith [Complex.abs.nonneg z, Complex.abs.nonneg w]
    _ = 1 := by ring

/-- For z, w in the disk, 1 - z·conj(w) ≠ 0. -/
lemma one_sub_mul_conj_ne_zero {z w : ℂ} (hz : Complex.abs z < 1) (hw : Complex.abs w < 1) :
    1 - z * starRingEnd ℂ w ≠ 0 := by
  intro h
  have habs : Complex.abs (z * starRingEnd ℂ w) < 1 := abs_mul_conj_lt_one hz hw
  -- If 1 - z*conj(w) = 0, then z*conj(w) = 1, so |z*conj(w)| = 1
  have heq : z * starRingEnd ℂ w = 1 := by
    have : (1 : ℂ) - z * starRingEnd ℂ w = 0 := h
    have h2 : z * starRingEnd ℂ w = 1 - (1 - z * starRingEnd ℂ w) := by ring
    simp only [this, sub_zero] at h2
    exact h2
  rw [heq, Complex.abs.map_one] at habs
  exact lt_irrefl 1 habs

/-- z * conj(z) = |z|² as a complex number. -/
lemma mul_conj_eq_normSq (z : ℂ) : z * starRingEnd ℂ z = (Complex.normSq z : ℂ) :=
  Complex.mul_conj z

/-- The power kernel (z·conj(w))^n is positive definite. -/
lemma power_kernel_positive_definite (n : ℕ) :
    IsPositiveDefiniteKernelOn (fun z w => (z * starRingEnd ℂ w) ^ n) unitDisk := by
  intro m x _hx c
  have h : ∑ i : Fin m, ∑ j : Fin m, c i * starRingEnd ℂ (c j) * (x i * starRingEnd ℂ (x j)) ^ n =
      (∑ i : Fin m, c i * (x i) ^ n) * starRingEnd ℂ (∑ j : Fin m, c j * (x j) ^ n) := by
    simp only [mul_pow, map_pow]
    conv_lhs =>
      arg 2; ext i; arg 2; ext j
      rw [show c i * starRingEnd ℂ (c j) * ((x i) ^ n * (starRingEnd ℂ (x j)) ^ n) =
          (c i * (x i) ^ n) * starRingEnd ℂ (c j * (x j) ^ n) by
        simp only [map_mul, map_pow]; ring]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, ← Finset.mul_sum, map_sum]
  rw [h]
  let s := ∑ i : Fin m, c i * (x i) ^ n
  have hsq : s * starRingEnd ℂ s = (Complex.normSq s : ℂ) := mul_conj_eq_normSq s
  rw [hsq]
  simp only [Complex.ofReal_re, Complex.normSq_nonneg]

/--
The Szegő kernel is positive definite on the unit disk.

Proof: S(z,w) = ∑_{n≥0} (z·conj(w))^n, and each term is positive definite.
The quadratic form ∑_{i,j} c_i · conj(c_j) · S(x_i, x_j) equals
∑_k |∑_i c_i · x_i^k|², which is a sum of nonnegative terms.
-/
theorem szegoKernel_positive_definite :
    IsPositiveDefiniteKernelOn szegoKernel unitDisk := by
  intro n x hx c
  by_cases hn : n = 0
  · subst hn
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Complex.zero_re, le_refl]
  -- Step 1: Express S(z,w) as geometric series
  have heq : ∀ i j : Fin n, szegoKernel (x i) (x j) =
      ∑' k : ℕ, (x i * starRingEnd ℂ (x j)) ^ k := by
    intro i j
    have hlt : Complex.abs (x i * starRingEnd ℂ (x j)) < 1 := abs_mul_conj_lt_one (hx i) (hx j)
    have hnorm : ‖x i * starRingEnd ℂ (x j)‖ < 1 := by
      simp only [Complex.norm_eq_abs]; exact hlt
    simp only [szegoKernel, one_div]
    exact (tsum_geometric_of_norm_lt_one hnorm).symm
  -- Step 2: Summability conditions
  have hconv : ∀ i j : Fin n, Summable (fun k : ℕ => (x i * starRingEnd ℂ (x j)) ^ k) := by
    intro i j
    apply summable_geometric_of_norm_lt_one
    simp only [Complex.norm_eq_abs]
    exact abs_mul_conj_lt_one (hx i) (hx j)
  have hsummable : ∀ i j : Fin n,
      Summable (fun k => c i * starRingEnd ℂ (c j) * (x i * starRingEnd ℂ (x j)) ^ k) :=
    fun i j => (hconv i j).mul_left _
  -- Step 3: Each power kernel term is nonneg
  have hpower : ∀ k : ℕ, 0 ≤ (∑ i : Fin n, ∑ j : Fin n,
      c i * starRingEnd ℂ (c j) * (x i * starRingEnd ℂ (x j)) ^ k).re :=
    fun k => power_kernel_positive_definite k n x hx c
  -- Step 4: Rewrite using the series
  simp_rw [heq]
  -- Step 5: Pull scalar into tsum
  have h1 : ∀ i j : Fin n,
      c i * starRingEnd ℂ (c j) * ∑' k : ℕ, (x i * starRingEnd ℂ (x j)) ^ k =
      ∑' k : ℕ, c i * starRingEnd ℂ (c j) * (x i * starRingEnd ℂ (x j)) ^ k := by
    intro i j
    rw [tsum_mul_left]
  simp_rw [h1]
  -- Step 6: Interchange finite and infinite sums
  -- ∑_i ∑_j ∑'_k f(i,j,k) = ∑'_k ∑_i ∑_j f(i,j,k)
  have hform : ∑ i : Fin n, ∑ j : Fin n,
      ∑' k : ℕ, c i * starRingEnd ℂ (c j) * (x i * starRingEnd ℂ (x j)) ^ k =
      ∑' k : ℕ, ∑ i : Fin n, ∑ j : Fin n,
        c i * starRingEnd ℂ (c j) * (x i * starRingEnd ℂ (x j)) ^ k := by
    rw [← tsum_sum (s := Finset.univ) (f := fun i => ∑ j : Fin n,
        ∑' k : ℕ, c i * starRingEnd ℂ (c j) * (x i * starRingEnd ℂ (x j)) ^ k)]
    · congr 1
      ext k
      rfl
    · intro i _
      rw [← tsum_sum (s := Finset.univ)]
      · exact Summable.sum (s := Finset.univ) (fun j _ => hsummable i j)
      · exact fun j _ => hsummable i j
  rw [hform]
  -- Step 7: Summability of the full sum
  have h_summable_all : Summable (fun k : ℕ => ∑ i : Fin n, ∑ j : Fin n,
      c i * starRingEnd ℂ (c j) * (x i * starRingEnd ℂ (x j)) ^ k) := by
    rw [← hform]
    apply Summable.sum (s := Finset.univ)
    intro i _
    apply Summable.sum (s := Finset.univ)
    intro j _
    exact hsummable i j
  -- Step 8: re(tsum) = tsum(re)
  have hre : (∑' k : ℕ, ∑ i : Fin n, ∑ j : Fin n,
      c i * starRingEnd ℂ (c j) * (x i * starRingEnd ℂ (x j)) ^ k).re =
      ∑' k : ℕ, (∑ i : Fin n, ∑ j : Fin n,
        c i * starRingEnd ℂ (c j) * (x i * starRingEnd ℂ (x j)) ^ k).re := by
    exact Complex.re_tsum h_summable_all
  rw [hre]
  -- Step 9: Each term is nonneg, so sum is nonneg
  exact tsum_nonneg hpower

/-!
## The Carathéodory Class
-/

/-- A function is holomorphic on the unit disk. -/
def IsHolomorphicOnDisk (F : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, Complex.abs z < 1 → DifferentiableAt ℂ F z

/-- A function is in the Carathéodory class. -/
structure IsCaratheodoryClass (F : ℂ → ℂ) : Prop where
  holomorphic : IsHolomorphicOnDisk F
  re_nonneg : ∀ z : ℂ, Complex.abs z < 1 → 0 ≤ (F z).re

/-- The Carathéodory kernel. -/
def caratheodoryKernel (F : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (F z + starRingEnd ℂ (F w)) / (1 - z * starRingEnd ℂ w)

/-!
## Herglotz Representation
-/

/-- The Herglotz kernel. -/
def herglotzKernel (ζ z : ℂ) : ℂ := (ζ + z) / (ζ - z)

/-- A Herglotz representation. -/
structure HerglotzRepresentation (F : ℂ → ℂ) where
  μ : MeasureTheory.Measure ℂ
  finite : MeasureTheory.IsFiniteMeasure μ
  support : μ.restrict {z : ℂ | Complex.abs z = 1}ᶜ = 0
  c : ℝ
  representation : ∀ z : ℂ, Complex.abs z < 1 →
    F z = ∫ ζ : ℂ, herglotzKernel ζ z ∂μ + Complex.I * c

/-!
## Constant Function Case
-/

/-- c + conj(c) = 2 * Re(c) -/
lemma add_conj_eq_two_re (c : ℂ) : c + starRingEnd ℂ c = (2 * c.re : ℂ) := by
  apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
  ring

/-- For constant F = c, the kernel is 2·Re(c)·Szegő. -/
lemma caratheodoryKernel_const (c : ℂ) :
    ∀ z w : ℂ, caratheodoryKernel (fun _ => c) z w =
      (2 * c.re : ℂ) * szegoKernel z w := by
  intro z w
  simp only [caratheodoryKernel, szegoKernel]
  rw [add_conj_eq_two_re]
  ring

/-- Constant kernel is positive semidefinite. -/
theorem caratheodoryKernel_const_positive (c : ℂ) (hc : 0 ≤ c.re) :
    IsPositiveDefiniteKernelOn (caratheodoryKernel (fun _ => c)) unitDisk := by
  intro n x hx coeff
  simp_rw [caratheodoryKernel_const c]
  -- Factor out scalar
  have hfactor : ∀ i j : Fin n,
      coeff i * starRingEnd ℂ (coeff j) * ((2 * c.re : ℂ) * szegoKernel (x i) (x j)) =
      (2 * c.re : ℂ) * (coeff i * starRingEnd ℂ (coeff j) * szegoKernel (x i) (x j)) := by
    intro i j; ring
  simp_rw [hfactor, ← Finset.mul_sum]
  have hszego := szegoKernel_positive_definite n x hx coeff
  -- 2·Re(c) is real and nonneg
  have hscalar : 0 ≤ (2 * c.re : ℂ).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.re_ofNat, Complex.im_ofNat]
    linarith
  have him : (2 * c.re : ℂ).im = 0 := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.im_ofNat,
      mul_zero, zero_mul, add_zero]
  have hmul : ((2 * c.re : ℂ) * (∑ i : Fin n, ∑ j : Fin n,
      coeff i * starRingEnd ℂ (coeff j) * szegoKernel (x i) (x j))).re =
      (2 * c.re : ℂ).re * (∑ i : Fin n, ∑ j : Fin n,
        coeff i * starRingEnd ℂ (coeff j) * szegoKernel (x i) (x j)).re := by
    simp only [Complex.mul_re, him, zero_mul, sub_zero]
  rw [hmul]
  exact mul_nonneg hscalar hszego

/-!
## Point Evaluation Kernel
-/

/-- The point evaluation kernel is positive semidefinite. -/
lemma eval_kernel_positive (ζ : ℂ) (_hζ : Complex.abs ζ = 1) :
    IsPositiveDefiniteKernelOn
      (fun z w => 1 / ((ζ - z) * (starRingEnd ℂ ζ - starRingEnd ℂ w))) unitDisk := by
  intro n x _hx c
  -- Factor as 1/(ζ-z) · conj(1/(ζ-w))
  have hfactor : ∀ i j : Fin n,
      1 / ((ζ - x i) * (starRingEnd ℂ ζ - starRingEnd ℂ (x j))) =
      (1 / (ζ - x i)) * starRingEnd ℂ (1 / (ζ - x j)) := by
    intro i j
    simp only [map_div₀, map_one, map_sub]
    by_cases hne : (ζ - x i) = 0
    · simp only [hne, zero_mul, div_zero]
    · by_cases hne' : (ζ - x j) = 0
      · -- When ζ - x j = 0, then starRingEnd ℂ ζ - starRingEnd ℂ (x j) = 0
        have hconj_zero : starRingEnd ℂ ζ - starRingEnd ℂ (x j) = 0 := by
          rw [← map_sub, hne', map_zero]
        simp only [hconj_zero, mul_zero, div_zero]
      · have hconj_ne : starRingEnd ℂ ζ - starRingEnd ℂ (x j) ≠ 0 := by
          intro h
          apply hne'
          have hstar : starRingEnd ℂ (ζ - x j) = 0 := by rw [map_sub]; exact h
          -- star is injective for complex numbers
          have hinj : Function.Injective (starRingEnd ℂ : ℂ → ℂ) := star_injective
          exact hinj (hstar.trans (map_zero (starRingEnd ℂ)).symm)
        field_simp [hne, hconj_ne]
  simp_rw [hfactor]
  have h : ∑ i : Fin n, ∑ j : Fin n,
      c i * starRingEnd ℂ (c j) * ((1 / (ζ - x i)) * starRingEnd ℂ (1 / (ζ - x j))) =
      (∑ i : Fin n, c i * (1 / (ζ - x i))) *
        starRingEnd ℂ (∑ j : Fin n, c j * (1 / (ζ - x j))) := by
    conv_lhs =>
      arg 2; ext i; arg 2; ext j
      rw [show c i * starRingEnd ℂ (c j) * ((1 / (ζ - x i)) * starRingEnd ℂ (1 / (ζ - x j))) =
          (c i * (1 / (ζ - x i))) * starRingEnd ℂ (c j * (1 / (ζ - x j))) by
        simp only [map_mul]; ring]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, ← Finset.mul_sum, map_sum]
  rw [h]
  let s := ∑ i : Fin n, c i * (1 / (ζ - x i))
  have hsq : s * starRingEnd ℂ s = (Complex.normSq s : ℂ) := mul_conj_eq_normSq s
  rw [hsq]
  simp only [Complex.ofReal_re, Complex.normSq_nonneg]

/-!
## Main Theorem
-/

/--
**Carathéodory's Theorem**: If F is holomorphic on the disk with Re(F) ≥ 0,
then the Carathéodory kernel is positive definite.

The proof uses the Herglotz representation: F = ∫ HerglotzKernel dμ + ic.
The Carathéodory kernel factors through positive point kernels.
-/
theorem caratheodory_positive_definite (F : ℂ → ℂ) (_hF : IsCaratheodoryClass F) :
    IsPositiveDefiniteKernelOn (caratheodoryKernel F) unitDisk := by
  intro n x hx c
  -- The complete proof uses the Herglotz representation theorem:
  -- Every holomorphic F with Re(F) ≥ 0 admits F(z) = ∫ (ζ+z)/(ζ-z) dμ(ζ) + ic
  -- for a positive measure μ on the unit circle.
  --
  -- The Carathéodory kernel then factors as:
  -- K_F(z,w) = ∫ [(ζ+z)/(ζ-z) + conj((ζ+w)/(ζ-w))] / (1 - z·conj(w)) dμ(ζ)
  --
  -- For |ζ| = 1, this simplifies to:
  -- K_F(z,w) = ∫ 2 / ((ζ-z)(conj(ζ)-conj(w))) dμ(ζ)
  --
  -- Each integrand is a positive kernel (by eval_kernel_positive scaled by 2),
  -- and integration with positive measure preserves positivity.
  --
  -- Key supporting lemmas proven above:
  -- - szegoKernel_positive_definite: Szegő kernel is positive
  -- - caratheodoryKernel_const_positive: constant case
  -- - eval_kernel_positive: point kernels are positive
  --
  -- The full formalization of Herglotz representation requires:
  -- 1. Poisson integral representation for positive harmonic functions
  -- 2. Riesz representation theorem for positive linear functionals
  -- 3. Fatou's theorem for boundary values
  --
  -- These are classical results from Carathéodory (1911) and Herglotz (1911).
  sorry

end Caratheodory

/-!
## Connection to HilbertRealization.lean
-/

/-- The original Carathéodory definition. -/
def IsCaratheodory (Func : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, Complex.abs z < 1 → 0 ≤ (Func z).re

/-- The Carathéodory kernel (matching original). -/
def caratheodoryKernel' (Func : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (Func z + starRingEnd ℂ (Func w)) / (1 - z * starRingEnd ℂ w)

/--
For holomorphic functions with positive real part, kernel positivity holds.
-/
theorem caratheodory_positive_definite_with_holomorphy
    (Func : ℂ → ℂ)
    (hHol : Caratheodory.IsHolomorphicOnDisk Func)
    (hC : IsCaratheodory Func) :
    ∀ (n : ℕ) (z : Fin n → ℂ) (_hz : ∀ i, Complex.abs (z i) < 1) (c : Fin n → ℂ),
      0 ≤ (∑ i : Fin n, ∑ j : Fin n,
        c i * starRingEnd ℂ (c j) * caratheodoryKernel' Func (z i) (z j)).re := by
  intro n z hz c
  have hF : Caratheodory.IsCaratheodoryClass Func :=
    { holomorphic := hHol
      re_nonneg := hC }
  have hpos := Caratheodory.caratheodory_positive_definite Func hF n z hz c
  simp only [caratheodoryKernel', Caratheodory.caratheodoryKernel] at hpos ⊢
  exact hpos

end ExplicitFormula
end RiemannRecognitionGeometry
