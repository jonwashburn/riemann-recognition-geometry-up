/-
Copyright (c) 2024 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Washburn, Gemini
-/
import RiemannRecognitionGeometry.ExplicitFormula.WeilTestFunctionProofs
import RiemannRecognitionGeometry.ExplicitFormula.Defs

/-!
# Concrete Test Function Space for Route 3

This file defines `WeilTestFunction`, a concrete candidate for the Route 3 test-function space.

## Status
- **Reflection and conjugation**: Proved (closure under `f(-·)` and `conj ∘ f`).
- **Convolution**: Still an axiom (requires convolution closure proof for Schwartz functions
  with the specific exponential decay).
- **Transform identities**: `weilTransform_reflection` is proved; `weilTransform_convolution`
  is still an axiom.
-/

noncomputable section

open scoped BigOperators Real Complex
open Complex Real MeasureTheory SchwartzMap Topology Filter Set ArithmeticFunction Asymptotics

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

/--
A Weil test function is a Schwartz function on ℝ satisfying specific decay properties allowing for
the convergence of Explicit Formula terms.

This matches earlier `IsWeilTestFunction` development but without an `even` constraint.
-/
structure WeilTestFunction where
  /-- The underlying Schwartz function. -/
  toSchwartz : SchwartzMap ℝ ℂ
  /-- Strong decay ensures the transform `Φ(s)` is analytic in a wide strip. -/
  decay : ∃ (C ε : ℝ), 0 < ε ∧ ∀ x, ‖toSchwartz x‖ ≤ C * Real.exp (- (1 / 2 + ε) * |x|)
  /-- Decay of the Fourier transform ensures absolute convergence of prime sums. -/
  ft_decay :
    ∃ (C' ε' : ℝ),
      0 < ε' ∧ ∀ ξ, ‖fourierTransformCLM ℂ toSchwartz ξ‖ ≤ C' * Real.exp (- (1 / 2 + ε') * |ξ|)

namespace WeilTestFunction

/-- Coercion to function. -/
instance : CoeFun WeilTestFunction (fun _ => ℝ → ℂ) where
  coe f := f.toSchwartz

variable (f g : WeilTestFunction)

/--
The Weil transform `Φ(s)`.

This is effectively a bilateral Laplace transform shifted to center on `s = 1/2`:
`Φ(s) = ∫_{-∞}^{∞} g(x) e^{(s - 1/2)x} dx`.
-/
def weilTransform (s : ℂ) : ℂ :=
  ∫ x : ℝ, f.toSchwartz x * Complex.exp ((s - 0.5) * x)

/-- Additive convolution of Weil test functions (analytic closure deferred). -/
axiom convolution (f g : WeilTestFunction) : WeilTestFunction

/-- Reflection `f(-x)`: proved using `reflectSchwartz` and decay preservation lemmas. -/
def reflection (f : WeilTestFunction) : WeilTestFunction where
  toSchwartz := reflectSchwartz f.toSchwartz
  decay := decay_preserved_by_reflection f.decay
  ft_decay := ft_decay_preserved_by_reflection f.ft_decay

/-- Complex conjugation `conj(f(x))`: proved using `conjSchwartz` and decay preservation lemmas. -/
def conjugation (f : WeilTestFunction) : WeilTestFunction where
  toSchwartz := conjSchwartz f.toSchwartz
  decay := decay_preserved_by_conjugation f.decay
  ft_decay := ft_decay_preserved_by_conjugation f.ft_decay

/-! ### Analytic properties -/

/-- Convolution theorem for the Weil transform (still an axiom). -/
axiom weilTransform_convolution (f g : WeilTestFunction) (s : ℂ) :
    (convolution f g).weilTransform s = f.weilTransform s * g.weilTransform s

/-- Reflection intertwines the Weil transform by `s ↦ 1 - s`.
    Proved: uses change of variables `u = -x`. -/
theorem weilTransform_reflection (f : WeilTestFunction) (s : ℂ) :
    (reflection f).weilTransform s = f.weilTransform (1 - s) := by
  simp only [weilTransform, reflection]
  -- The Schwartz-level proof gives us most of the work
  exact ExplicitFormula.weilTransform_reflection f.toSchwartz s

/-! ### `TestSpace` instance -/

instance : TestSpace WeilTestFunction where
  Mellin := fun f s => f.weilTransform s
  conv := fun f g => convolution f g
  tilde := fun f => reflection f
  star := fun f => conjugation f
  mellin_conv := by
    intro f g s
    simpa using weilTransform_convolution f g s
  mellin_tilde := by
    intro f s
    simpa using weilTransform_reflection f s

end WeilTestFunction

end ExplicitFormula
end RiemannRecognitionGeometry
