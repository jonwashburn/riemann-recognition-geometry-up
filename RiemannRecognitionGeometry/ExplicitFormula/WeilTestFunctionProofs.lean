/-
Copyright (c) 2024 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Washburn
-/
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.VonMangoldt
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.VitaliCaratheodory
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Proof Components for WeilTestFunction

This file provides the proofs that `WeilTestFunction` is closed under
reflection and conjugation, along with the corresponding transform identities.

## Main Results

* `reflectSchwartz` - Reflection of a Schwartz function is Schwartz
* `conjSchwartz` - Complex conjugation of a Schwartz function is Schwartz
* `decay_preserved_by_reflection` - Exponential decay is preserved under reflection
* `decay_preserved_by_conjugation` - Exponential decay is preserved under conjugation
* `weilTransform_reflection` - The Weil transform satisfies `Φ(f(-·))(s) = Φ(f)(1-s)`

## Status

- **Reflection and conjugation**: Fully proved for Schwartz functions.
- **Decay preservation**: Fully proved for both function and Fourier decay.
- **Fourier transform identities**: Fully proved (`ℱ[f(-·)](ξ) = ℱ[f](-ξ)` and
  `ℱ[conj ∘ f](ξ) = conj(ℱ[f](-ξ))`).
- **Convolution**: Not proved here; requires separate development.
-/

noncomputable section

open scoped BigOperators Real Complex
open Complex Real MeasureTheory SchwartzMap Topology Filter Set ArithmeticFunction Asymptotics

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

/-! ## Basic Definitions -/

/-- The reflection equivalence on ℝ: x ↦ -x -/
def negEquiv : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.neg ℝ

/-- Key identity: `starRingEnd ℂ` equals `Complex.conjCLE` as functions. -/
lemma starRingEnd_eq_conjCLE : (starRingEnd ℂ : ℂ → ℂ) = Complex.conjCLE := rfl

/-! ## Schwartz Function Constructions -/

/-- Complex conjugation of a Schwartz function: `f ↦ conj ∘ f`.

This is proved by showing that `Complex.conjCLE` (complex conjugation as a
continuous ℝ-linear equivalence) preserves smoothness and decay properties. -/
def conjSchwartz (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ := {
  toFun := fun x => starRingEnd ℂ (f x)
  smooth' := by
    refine ContDiff.comp ?_ f.smooth'
    exact Complex.conjCLE.contDiff
  decay' := fun k n => by
    obtain ⟨C, hC⟩ := f.decay' k n
    use C
    intro x
    have hsmooth_at := f.smooth'.contDiffAt (x := x)
    have heq : (fun x => starRingEnd ℂ (f x)) = (Complex.conjCLE : ℂ → ℂ) ∘ f.toFun := rfl
    rw [heq]
    have hn_le : (n : WithTop ℕ∞) ≤ (⊤ : ℕ∞) := WithTop.coe_le_coe.mpr le_top
    have hderiv := ContinuousLinearMap.iteratedFDeriv_comp_left
        Complex.conjCLE.toContinuousLinearMap hsmooth_at (i := n) hn_le
    simp only [ContinuousLinearEquiv.coe_coe] at hderiv
    rw [hderiv]
    calc ‖x‖ ^ k * ‖Complex.conjCLE.toContinuousLinearMap.compContinuousMultilinearMap
            (iteratedFDeriv ℝ n f.toFun x)‖
        ≤ ‖x‖ ^ k * (‖Complex.conjCLE.toContinuousLinearMap‖ *
            ‖iteratedFDeriv ℝ n f.toFun x‖) := by
          gcongr
          exact ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
      _ ≤ ‖x‖ ^ k * (1 * ‖iteratedFDeriv ℝ n f.toFun x‖) := by
          gcongr
          have : ‖Complex.conjCLE.toContinuousLinearMap‖ ≤ 1 := by
            rw [ContinuousLinearMap.opNorm_le_iff (by norm_num : (0:ℝ) ≤ 1)]
            intro z
            simp [Complex.abs_conj]
          exact this
      _ = ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f.toFun x‖ := by ring
      _ ≤ C := hC x
}

/-- Reflection of a Schwartz function: `f ↦ f(-·)`.

This uses `compCLMOfContinuousLinearEquiv` with the negation equivalence. -/
def reflectSchwartz (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ) f

/-- Evaluation lemma for reflected Schwartz functions. -/
lemma reflectSchwartz_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    reflectSchwartz f x = f (-x) := by
  simp only [reflectSchwartz, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
             ContinuousLinearEquiv.neg_apply, ContinuousLinearEquiv.coe_coe]
  rfl

/-- Evaluation lemma for conjugated Schwartz functions. -/
lemma conjSchwartz_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    conjSchwartz f x = starRingEnd ℂ (f x) := rfl

/-! ## Weil Transform -/

/-- The Weil transform `Φ(s)`: a bilateral Laplace transform centered at `s = 1/2`. -/
def weilTransform (f : SchwartzMap ℝ ℂ) (s : ℂ) : ℂ :=
  ∫ x : ℝ, f x * Complex.exp ((s - 0.5) * x)

/-- Reflection intertwines the Weil transform by `s ↦ 1 - s`.

This is the key transform identity: `Φ(f(-·))(s) = Φ(f)(1 - s)`.

The proof uses the substitution `u = -x` and the fact that
`(s - 1/2) * (-u) = (1 - s - 1/2) * u`. -/
lemma weilTransform_reflection (f : SchwartzMap ℝ ℂ) (s : ℂ) :
    weilTransform (reflectSchwartz f) s = weilTransform f (1 - s) := by
  simp only [weilTransform]
  have h1 : ∀ x, reflectSchwartz f x = f (-x) := reflectSchwartz_apply f
  simp only [h1]
  have h2 : ∫ (x : ℝ), f (-x) * Complex.exp ((s - 0.5) * ↑x) =
            ∫ (u : ℝ), f u * Complex.exp ((s - 0.5) * ↑(-u)) := by
    rw [← integral_neg_eq_self (fun u => f u * Complex.exp ((s - 0.5) * ↑(-u)))]
    simp only [neg_neg]
  rw [h2]
  congr 1
  ext u
  congr 1
  simp only [Complex.ofReal_neg, mul_neg]
  ring

/-! ## Decay Preservation -/

/-- Reflection preserves exponential decay. -/
lemma decay_preserved_by_reflection {f : SchwartzMap ℝ ℂ}
    (hdecay : ∃ (C ε : ℝ), 0 < ε ∧ ∀ x, ‖f x‖ ≤ C * Real.exp (- (1 / 2 + ε) * |x|)) :
    ∃ (C ε : ℝ), 0 < ε ∧ ∀ x, ‖reflectSchwartz f x‖ ≤ C * Real.exp (- (1 / 2 + ε) * |x|) := by
  obtain ⟨C, ε, hε, hbound⟩ := hdecay
  refine ⟨C, ε, hε, ?_⟩
  intro x
  rw [reflectSchwartz_apply]
  have h := hbound (-x)
  simp only [abs_neg] at h
  exact h

/-- Conjugation preserves exponential decay. -/
lemma decay_preserved_by_conjugation {f : SchwartzMap ℝ ℂ}
    (hdecay : ∃ (C ε : ℝ), 0 < ε ∧ ∀ x, ‖f x‖ ≤ C * Real.exp (- (1 / 2 + ε) * |x|)) :
    ∃ (C ε : ℝ), 0 < ε ∧ ∀ x, ‖conjSchwartz f x‖ ≤ C * Real.exp (- (1 / 2 + ε) * |x|) := by
  obtain ⟨C, ε, hε, hbound⟩ := hdecay
  refine ⟨C, ε, hε, ?_⟩
  intro x
  rw [conjSchwartz_apply]
  rw [Complex.norm_eq_abs, Complex.abs_conj, ← Complex.norm_eq_abs]
  exact hbound x

/-! ## Fourier Transform Properties

The following lemmas relate Fourier transforms of reflected/conjugated functions.
These are standard results in Fourier analysis:
- `ℱ[f(-·)](ξ) = ℱ[f](-ξ)`
- `ℱ[conj ∘ f](ξ) = conj(ℱ[f](-ξ))`
-/

/-- The Fourier integral of a reflected function equals the Fourier integral at the negated frequency.
This is a key property: `ℱ[f(-·)](w) = ℱ[f](-w)`.
The proof uses the substitution `u = -v` and the invariance of Lebesgue measure under negation. -/
lemma Real_fourierIntegral_comp_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℝ → E) (w : ℝ) :
    Real.fourierIntegral (f ∘ Neg.neg) w = Real.fourierIntegral f (-w) := by
  simp only [Real.fourierIntegral, VectorFourier.fourierIntegral, Function.comp_apply]
  -- Use substitution u = -v, which is valid since Lebesgue measure is invariant under negation
  have h : ∫ (v : ℝ), Real.fourierChar (-((innerₗ ℝ) v) w) • f (-v) =
           ∫ (u : ℝ), Real.fourierChar (-((innerₗ ℝ) (-u)) w) • f u := by
    rw [← integral_neg_eq_self]
    simp only [neg_neg]
  rw [h]
  congr 1
  ext u
  congr 1
  congr 1
  -- The key algebraic identity: -(innerₗ ℝ (-u) w) = -(innerₗ ℝ u (-w))
  -- Both equal inner u w since inner is bilinear and we have double negation
  simp only [innerₗ_apply, inner_neg_left, inner_neg_right, neg_neg]

/-- The Fourier transform of a reflected Schwartz function. -/
lemma fourierTransform_reflect (f : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    fourierTransformCLM ℂ (reflectSchwartz f) ξ = fourierTransformCLM ℂ f (-ξ) := by
  simp only [fourierTransformCLM_apply]
  -- Show that reflectSchwartz gives f ∘ neg
  have h : (reflectSchwartz f : ℝ → ℂ) = (f : ℝ → ℂ) ∘ Neg.neg := by
    ext x
    simp only [reflectSchwartz, compCLMOfContinuousLinearEquiv_apply,
               ContinuousLinearEquiv.neg_apply, ContinuousLinearEquiv.coe_coe,
               Function.comp_apply]
  rw [h]
  exact Real_fourierIntegral_comp_neg (f : ℝ → ℂ) ξ

/-- Fourier decay is preserved under reflection. -/
lemma ft_decay_preserved_by_reflection {f : SchwartzMap ℝ ℂ}
    (hft_decay : ∃ (C' ε' : ℝ), 0 < ε' ∧
      ∀ ξ, ‖fourierTransformCLM ℂ f ξ‖ ≤ C' * Real.exp (- (1 / 2 + ε') * |ξ|)) :
    ∃ (C' ε' : ℝ), 0 < ε' ∧
      ∀ ξ, ‖fourierTransformCLM ℂ (reflectSchwartz f) ξ‖ ≤ C' * Real.exp (- (1 / 2 + ε') * |ξ|) := by
  obtain ⟨C', ε', hε', hbound⟩ := hft_decay
  refine ⟨C', ε', hε', ?_⟩
  intro ξ
  rw [fourierTransform_reflect]
  have h := hbound (-ξ)
  simp only [abs_neg] at h
  exact h

/-- For elements on the unit circle, complex conjugation equals the inverse.
This follows from the fact that `z * conj(z) = |z|² = 1` for `|z| = 1`. -/
lemma Real_fourierChar_conj (t : ℝ) :
    starRingEnd ℂ (Real.fourierChar t : ℂ) = Real.fourierChar (-t) := by
  have h := Circle.coe_inv_eq_conj (Real.fourierChar t)
  rw [← h]
  congr 1
  exact (Real.fourierChar.map_neg_eq_inv t).symm

/-- The Fourier integral of a conjugated function.
The key identity is `ℱ[conj ∘ f](w) = conj(ℱ[f](-w))`.
This uses that `conj(e^{2πit}) = e^{-2πit}` and that conjugation commutes with integration. -/
lemma Real_fourierIntegral_conj (f : ℝ → ℂ) (w : ℝ) :
    Real.fourierIntegral (starRingEnd ℂ ∘ f) w = starRingEnd ℂ (Real.fourierIntegral f (-w)) := by
  simp only [Real.fourierIntegral, VectorFourier.fourierIntegral, Function.comp_apply]
  simp only [Circle.smul_def, smul_eq_mul]
  -- Key step: show the integrands are related by conjugation
  have heq : ∀ v, (Real.fourierChar (-(innerₗ ℝ v w)) : ℂ) * (starRingEnd ℂ (f v)) =
             starRingEnd ℂ ((Real.fourierChar (-(innerₗ ℝ v (-w))) : ℂ) * f v) := by
    intro v
    rw [map_mul]
    congr 1
    -- The character transforms: conj(e^{2πi(vw)}) = e^{-2πi(vw)} = e^{2πi(-(vw))}
    rw [Real_fourierChar_conj (-(innerₗ ℝ v (-w)))]
    simp only [innerₗ_apply, inner_neg_right, neg_neg]
  simp only [heq]
  -- Conjugation commutes with integration
  rw [← integral_conj]

/-- The Fourier transform of a conjugated Schwartz function.
This is proved using `Real_fourierIntegral_conj`. -/
lemma fourierTransform_conj (f : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    fourierTransformCLM ℂ (conjSchwartz f) ξ = starRingEnd ℂ (fourierTransformCLM ℂ f (-ξ)) := by
  simp only [fourierTransformCLM_apply]
  have h : (conjSchwartz f : ℝ → ℂ) = starRingEnd ℂ ∘ (f : ℝ → ℂ) := by
    ext x; exact conjSchwartz_apply f x
  rw [h]
  exact Real_fourierIntegral_conj (f : ℝ → ℂ) ξ

/-- Fourier decay is preserved under conjugation. -/
lemma ft_decay_preserved_by_conjugation {f : SchwartzMap ℝ ℂ}
    (hft_decay : ∃ (C' ε' : ℝ), 0 < ε' ∧
      ∀ ξ, ‖fourierTransformCLM ℂ f ξ‖ ≤ C' * Real.exp (- (1 / 2 + ε') * |ξ|)) :
    ∃ (C' ε' : ℝ), 0 < ε' ∧
      ∀ ξ, ‖fourierTransformCLM ℂ (conjSchwartz f) ξ‖ ≤ C' * Real.exp (- (1 / 2 + ε') * |ξ|) := by
  obtain ⟨C', ε', hε', hbound⟩ := hft_decay
  refine ⟨C', ε', hε', ?_⟩
  intro ξ
  rw [fourierTransform_conj]
  simp only [RingHomCompTriple.comp_apply, RingHom.id_apply, Complex.norm_eq_abs, Complex.abs_conj]
  have h := hbound (-ξ)
  simp only [abs_neg, Complex.norm_eq_abs] at h
  exact h

/-! ## Convolution

The additive convolution `(f ⋆ g)(x) = ∫ f(t) g(x-t) dt` is fundamental for the
Weil transform. The key theorem is that the Weil transform converts convolution
to pointwise multiplication.

**Note**: Proving that convolution of Schwartz functions is Schwartz, and that
it preserves the specific exponential decay conditions of WeilTestFunction,
requires substantial analytical machinery. The key results are sketched here.
-/

/-- Additive convolution of two Schwartz functions at a point.
This is the standard definition: `(f ⋆ g)(x) = ∫ f(t) g(x-t) dt`. -/
def schwartzConvAt (f g : SchwartzMap ℝ ℂ) (x : ℝ) : ℂ :=
  ∫ t : ℝ, f t * g (x - t)

/-- Schwartz functions are bounded. -/
lemma schwartz_bounded (g : SchwartzMap ℝ ℂ) : ∃ M, ∀ y, ‖g y‖ ≤ M := by
  obtain ⟨C, hC⟩ := g.decay' 0 0
  use C
  intro y
  specialize hC y
  simp only [pow_zero, one_mul] at hC
  -- The decay' condition gives bounds on iteratedFDeriv, which at n=0 is the function itself
  have h : ‖iteratedFDeriv ℝ 0 g.toFun y‖ = ‖g y‖ := by
    rw [iteratedFDeriv_zero_eq_comp]
    simp only [Function.comp_apply, LinearIsometryEquiv.norm_map]
    rfl
  rwa [h] at hC

/-- The convolution integrand is integrable for Schwartz functions.
This follows from the rapid decay of Schwartz functions. -/
lemma schwartzConv_integrable (f g : SchwartzMap ℝ ℂ) (x : ℝ) :
    Integrable (fun t => f t * g (x - t)) := by
  -- f is integrable and g is bounded, so the product is integrable
  have hf_int : Integrable (f : ℝ → ℂ) := f.integrable
  obtain ⟨M, hM⟩ := schwartz_bounded g
  have hM_pos : 0 ≤ M := by
    have := hM 0
    exact le_trans (norm_nonneg _) this
  -- Use Integrable.mono: bound ‖f(t) * g(x-t)‖ ≤ M * ‖f(t)‖
  have hf_norm_int : Integrable (fun t => M * ‖f t‖) := hf_int.norm.const_mul M
  apply Integrable.mono' hf_norm_int
  · exact hf_int.aestronglyMeasurable.mul
      (g.continuous.aestronglyMeasurable.comp_measurable (measurable_const.sub measurable_id))
  · filter_upwards with t
    calc ‖f t * g (x - t)‖ = ‖f t‖ * ‖g (x - t)‖ := norm_mul _ _
      _ ≤ ‖f t‖ * M := by gcongr; exact hM _
      _ = M * ‖f t‖ := mul_comm _ _

/-- The Weil transform of convolution as a double integral.
This is the first step towards the convolution theorem. -/
lemma weilTransform_convAt_eq (f g : SchwartzMap ℝ ℂ) (s : ℂ) :
    (∫ x : ℝ, schwartzConvAt f g x * Complex.exp ((s - 0.5) * x)) =
    ∫ x : ℝ, (∫ t : ℝ, f t * g (x - t)) * Complex.exp ((s - 0.5) * x) := by
  rfl

/-- The convolution theorem for the Weil transform (at function level).
`∫∫ f(t)g(x-t)e^{(s-1/2)x} dt dx = (∫ f(t)e^{(s-1/2)t} dt) * (∫ g(u)e^{(s-1/2)u} du)`

This is a standard result in harmonic analysis. The proof uses:
1. Fubini's theorem to swap the order of integration
2. Translation invariance of Lebesgue measure: `∫ h(x-t) dx = ∫ h(u) du`
3. The factorization `e^{(s-½)(u+t)} = e^{(s-½)u} · e^{(s-½)t}`
4. Separation of the double integral

**Key integrability requirement**: The integrand `f(t) · g(x-t) · e^{(s-½)x}` must be
integrable on ℝ × ℝ. For Schwartz functions f, g, this follows from:
- The function `x ↦ ∫_t ‖f(t) · g(x-t)‖ dt` is the convolution `‖f‖ ⋆ ‖g‖`.
- Since ‖f‖, ‖g‖ ∈ L¹(ℝ), their convolution is in L¹(ℝ) by Young's inequality.
- The exponential factor is controlled when `s` is in the strip of absolute convergence.

**Status**: This is a mathematically standard result. The formalization requires
showing product-measure integrability using `integrable_prod_iff` and the convolution
properties of L¹ functions in Mathlib.
-/
theorem weilTransform_schwartzConv (f g : SchwartzMap ℝ ℂ) (s : ℂ) :
    (∫ x : ℝ, schwartzConvAt f g x * Complex.exp ((s - 0.5) * x)) =
    weilTransform f s * weilTransform g s := by
  -- The proof structure is:
  -- 1. Distribute exp inside: ∫_x (∫_t f(t)g(x-t) dt) · e^{...} = ∫_x ∫_t f(t)g(x-t)e^{...} dt
  -- 2. Show integrability on ℝ × ℝ using:
  --    - `integrable_prod_iff`: need (a) pointwise integrability and (b) L¹ norm function
  --    - For (b): x ↦ ∫‖f(t)g(x-t)‖ dt = ‖f‖ ⋆ ‖g‖ ∈ L¹ by Young's convolution inequality
  -- 3. Apply Fubini to swap integrals
  -- 4. Change variables u = x - t using `integral_sub_right_eq_self`
  -- 5. Factor exp((s-½)(u+t)) = exp((s-½)u) · exp((s-½)t)
  -- 6. Separate and factor out constants
  sorry

end ExplicitFormula
end RiemannRecognitionGeometry
