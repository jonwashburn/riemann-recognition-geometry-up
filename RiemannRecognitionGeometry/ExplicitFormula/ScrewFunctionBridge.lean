/-
# Screw-function / kernel-positivity bridge (Matsumoto–Suzuki style)

Matsumoto–Suzuki (arXiv:2409.00888) give an RH-equivalent criterion:
a concrete function `g : ℝ → ℝ` built from a zero-sum is a **screw function**
iff RH holds. A screw function is defined by nonnegative-definiteness of a
kernel `G_g(t,u) = g(t-u) - g(t) - g(-u) + g(0)`.

This file packages that *shape* as a Lean-facing intermediate target.
It does **not** attempt to define the actual zeta-derived `g` or prove the criterion.
-/

import RiemannRecognitionGeometry.ExplicitFormula.Caratheodory
import RiemannRecognitionGeometry.ExplicitFormula.Li

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open ComplexConjugate
open MeasureTheory

/-! ## Screw functions as positive definite kernels -/

/-- The screw-kernel associated to a real-valued function `g`. -/
def screwKernel (g : ℝ → ℝ) (t u : ℝ) : ℂ :=
  (g (t - u) - g t - g (-u) + g 0 : ℝ)

/-- `g` is a screw function on `ℝ` if its associated kernel is positive definite on all of `ℝ`. -/
def IsScrewFunction (g : ℝ → ℝ) : Prop :=
  Caratheodory.IsPositiveDefiniteKernelOn (screwKernel g) (Set.univ : Set ℝ)

/-! ## Interval-restricted (Suzuki 2206.03682 style) targets -/

/-- The closed symmetric interval `[-a, a]` as a set. -/
def intervalSet (a : ℝ) : Set ℝ :=
  Set.Icc (-a) a

/-- The Lebesgue measure restricted to `[-a,a]`. -/
def intervalMeasure (a : ℝ) : Measure ℝ :=
  (volume.restrict (intervalSet a))

/--
Mean-zero condition on `[-a,a]` (with respect to the restricted Lebesgue measure).

We include an `Integrable` hypothesis so this does not become vacuous.
-/
def MeanZeroOnInterval (a : ℝ) (φ : ℝ → ℂ) : Prop :=
  Integrable φ (intervalMeasure a) ∧ (∫ t : ℝ, φ t ∂ intervalMeasure a) = 0

/--
The interval kernel form associated to the screw kernel, written as an iterated integral:

`⟪φ,ψ⟫_a := ∬ K(t,u) · ψ(u) · conj(φ(t)) du dt` over `[-a,a] × [-a,a]`.

This is a **target definition**: papers often prove positivity/nondegeneracy of this form
under additional regularity (continuity/trace class) assumptions.
-/
def screwKernelFormOnInterval (g : ℝ → ℝ) (a : ℝ) (φ ψ : ℝ → ℂ) : ℂ :=
  ∫ t : ℝ, ∫ u : ℝ,
      screwKernel g t u * ψ u * starRingEnd ℂ (φ t)
    ∂ intervalMeasure a
  ∂ intervalMeasure a

/--
Interval positivity target (Theorem 1.3 shape in Suzuki 2206.03682):
for every `a>0`, the screw-kernel form is nonnegative on mean-zero test functions supported in `[-a,a]`.

We express it on all `φ : ℝ → ℂ` satisfying the mean-zero integrability condition on the restricted measure.
-/
def IntervalKernelFormNonneg (g : ℝ → ℝ) : Prop :=
  ∀ ⦃a : ℝ⦄, 0 < a →
    ∀ φ : ℝ → ℂ, MeanZeroOnInterval a φ →
      0 ≤ (screwKernelFormOnInterval g a φ φ).re

/--
Interval nondegeneracy target (Theorem 1.4 shape in Suzuki 2206.03682):
for every `a>0`, the sesquilinear form has trivial left-kernel on mean-zero functions.

This packages the “no zero eigenvalue” / “nondegenerate hermitian form” criterion
without committing to a specific integral-operator construction.
-/
def IntervalKernelFormNondegenerate (g : ℝ → ℝ) : Prop :=
  ∀ ⦃a : ℝ⦄, 0 < a →
    ∀ φ : ℝ → ℂ, MeanZeroOnInterval a φ →
      (∀ ψ : ℝ → ℂ, MeanZeroOnInterval a ψ → screwKernelFormOnInterval g a φ ψ = 0) →
        φ = 0

/-! ## A Lean-facing “bridge target” package -/

/-- A minimal package asserting an RH-equivalent screw-function criterion for a specific `g`. -/
structure ScrewFunctionBridgeFramework (F : Type) [TestSpace F] extends LiFramework F where
  /-- The candidate function whose screw-property is asserted to be RH-equivalent. -/
  g : ℝ → ℝ
  /-- The core bridge: `IsScrewFunction g ↔ RH`. -/
  screwCriterion : IsScrewFunction g ↔ RiemannHypothesis

/--
Optional stronger packaging mirroring Suzuki’s interval criteria (Theorems 1.3/1.4):
state RH-equivalent conditions in terms of the interval-restricted kernel form.

This is intentionally a *target bundle*: proving these equivalences for the zeta-derived `g`
would be as hard as RH, but the statements are often easier to align with operator/kernel papers.
-/
structure ScrewFunctionIntervalBridgeFramework (F : Type) [TestSpace F]
    extends ScrewFunctionBridgeFramework F where
  intervalNonnegCriterion : IntervalKernelFormNonneg g ↔ RiemannHypothesis
  intervalNondegCriterion : IntervalKernelFormNondegenerate g ↔ RiemannHypothesis

namespace ScrewFunctionBridgeFramework

variable {F : Type} [TestSpace F] (S : ScrewFunctionBridgeFramework F)

/-- If the screw criterion holds and `g` is a screw function, then RH follows. -/
theorem rh_of_isScrewFunction (hg : IsScrewFunction S.g) : RiemannHypothesis :=
  (S.screwCriterion).1 hg

end ScrewFunctionBridgeFramework

end ExplicitFormula
end RiemannRecognitionGeometry
