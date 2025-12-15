/-
Copyright (c) 2024 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Washburn, Gemini
-/
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.VonMangoldt
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.VitaliCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Calculus.ParametricIntegral
import RiemannRecognitionGeometry.ExplicitFormula.Defs

/-!
# Concrete Test Function Space for Route 3

This file defines `WeilTestFunction`, a concrete candidate for the Route 3 test-function space.

The full analytic closure properties (closure under convolution/involution; transform identities;
Fubini/Tonelli justifications) are nontrivial and are **not** proved here yet.

Instead, we keep the interface stable by recording these as explicit axioms. Downstream files can
use `WeilTestFunction` as a `TestSpace`, while the hard analysis is proved (or further isolated)
later.
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

/-- Reflection `g(-x)` (analytic closure deferred). -/
axiom reflection (f : WeilTestFunction) : WeilTestFunction

/-- Complex conjugation (analytic closure deferred). -/
axiom conjugation (f : WeilTestFunction) : WeilTestFunction

/-! ### Analytic properties (recorded as axioms for now) -/

/-- Convolution theorem for the Weil transform. -/
axiom weilTransform_convolution (f g : WeilTestFunction) (s : ℂ) :
    (convolution f g).weilTransform s = f.weilTransform s * g.weilTransform s

/-- Reflection intertwines the Weil transform by `s ↦ 1 - s`. -/
axiom weilTransform_reflection (f : WeilTestFunction) (s : ℂ) :
    (reflection f).weilTransform s = f.weilTransform (1 - s)

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
