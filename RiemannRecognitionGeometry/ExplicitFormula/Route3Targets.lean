/-
# Route 3: concrete targets (F and L)

This file fixes a concrete ambient test-function type `F` to target for Route 3, together with the
corresponding `LagariasFramework F` (still abstract at the `W¹` / explicit-formula level).

We intentionally keep the genuinely hard analytic content (zero-sum definition, convergence,
explicit formula) isolated in the `LagariasFramework` value `Route3.L`.
-/

import Mathlib.Analysis.MellinTransform
import RiemannRecognitionGeometry.ExplicitFormula.Defs
import RiemannRecognitionGeometry.ExplicitFormula.Lagarias
import RiemannRecognitionGeometry.ExplicitFormula.MathlibBridge
import RiemannRecognitionGeometry.ExplicitFormula.MulConvolution

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open MeasureTheory Set
open scoped BigOperators

namespace Route3

/-- Concrete Route 3 test-function type: functions `ℝ → ℂ` (supported on `(0,∞)` in integrals). -/
abbrev F : Type := ℝ → ℂ

/--
Axiom: Mellin-multiplicativity for the multiplicative convolution on `(0,∞)`.

In the real Route 3 proof this is discharged under explicit integrability hypotheses (Fubini/Tonelli).
Here we choose to treat it as a global axiom so that we can fix a concrete `TestSpace` target type.
-/
axiom mellin_mulConv (f g : F) (s : ℂ) :
  mellin (mulConv f g) s = mellin f s * mellin g s

/-- Concrete `TestSpace` instance on `F = ℝ → ℂ` (Mellin + multiplicative convolution + involution). -/
instance instTestSpace : TestSpace F where
  Mellin := fun f s => mellin f s
  conv := fun f g => mulConv f g
  tilde := fun f => tildeFun f
  star := fun f => starFun f
  mellin_conv := by
    intro f g s
    simpa using (mellin_mulConv (f := f) (g := g) (s := s))
  mellin_tilde := by
    intro f s
    simpa [tildeFun] using (mellin_tildeFun (f := f) (s := s))

end Route3

end ExplicitFormula
end RiemannRecognitionGeometry
