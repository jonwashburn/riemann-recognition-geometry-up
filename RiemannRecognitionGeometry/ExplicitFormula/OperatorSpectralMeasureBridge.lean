/-
# Operator / spectral-measure intermediate target (Route 3)

Motivation (from `arXiv:2311.08519`):
- represent (truncated/completed) Weil explicit sums as **quadratic forms** of a self-adjoint operator,
- then (conceptually via the spectral theorem) rewrite those quadratic forms as **integrals against a
  spectral measure**.

In our Lean development, the end target shape is already:
- `SpectralIdentity` (quadratic-form integral with a nonnegative weight), and/or
- `SesqIntegralIdentity` / `SesqMeasureIntegralIdentity` (sesquilinear integral forms).

This file introduces a *typed intermediate target* that sits between:

`(operator realization)`  →  `(integral realization)`

so we can thread operator-theoretic arguments (and citations) through the same Route 3 pipeline.

This file does **not** prove the spectral theorem; it only packages the goal as a structure.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import RiemannRecognitionGeometry.ExplicitFormula.HilbertRealization

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open scoped InnerProductSpace
open MeasureTheory

section Sesquilinear

variable {F : Type} [TestSpace F] [AddCommGroup F] [Module ℂ F]

/-! ## Operator-form identity (sesquilinear form) -/

/-- Operator-form representation of the **sesquilinear** pairing `W¹(pair f g)`.

This is the natural operator-theoretic strengthening of `OperatorQuadraticIdentity`:
it matches the “kernel/inner-product” picture needed for reflection positivity and for
`SesqMeasureIntegralIdentity`.

We keep it as a *target structure*: no spectral theorem is invoked here. -/
structure OperatorSesqIdentity (L : LagariasFramework F) where
  /-- The Hilbert space in which the form lives. -/
  H : Type
  instNACG : NormedAddCommGroup H
  instIP : InnerProductSpace ℂ H
  instComplete : CompleteSpace H
  /-- Linear map sending test functions into the Hilbert space. -/
  T : F →ₗ[ℂ] H
  /-- A bounded operator generating the form (often multiplication by a real function). -/
  A : H →L[ℂ] H
  /-- Self-adjointness (so `⟪A x, y⟫` is the polarization of a real quadratic form). -/
  selfAdjoint : IsSelfAdjoint A
  /-- The sesquilinear identity. -/
  identity :
    ∀ f g : F, L.W1 (pair (F := F) f g) = ⟪A (T f), T g⟫_ℂ

/-! ## Spectral-measure-form identity (sesquilinear integral) -/

/-- A spectral-measure-form representation of the **sesquilinear** pairing, with a general weight `w`.

This is the sesquilinear analogue of `SpectralMeasureQuadraticIdentity`.  It is essentially the
same shape as `HilbertRealization.SesqIntegralIdentity`, but does not insist that `w = weightOfJ J`.

If you can identify `w = weightOfJ J`, you can translate it into the canonical Route‑3 integral target. -/
structure SpectralMeasureSesqIntegralIdentity (L : LagariasFramework F) where
  μ : Measure ℝ := volume
  w : ℝ → ℝ
  w_nonneg : ∀ t : ℝ, 0 ≤ w t
  transform : F →ₗ[ℂ] (ℝ → ℂ)
  /-- L² admissibility for the weighted transform. -/
  memL2 : ∀ f : F,
    MeasureTheory.Memℒp (fun t : ℝ => ((Real.sqrt (w t) : ℝ) : ℂ) * transform f t) 2 μ
  /-- Sesquilinear identity as a Bochner integral with weight `w`. -/
  identity_integral :
    ∀ f g : F,
      L.W1 (pair (F := F) f g) =
        ∫ t : ℝ, ((w t : ℝ) : ℂ) * ((starRingEnd ℂ (transform f t)) * (transform g t)) ∂ μ

namespace SpectralMeasureSesqIntegralIdentity

variable (L : LagariasFramework F) (S : SpectralMeasureSesqIntegralIdentity (F := F) (L := L))

/-- If you can identify `w` with the canonical `weightOfJ J`, you get a `SesqIntegralIdentity`. -/
def toSesqIntegralIdentity
    (J : ℂ → ℂ) (hw : ∀ t : ℝ, S.w t = HilbertRealization.weightOfJ J t) :
    HilbertRealization.SesqIntegralIdentity (F := F) (L := L) :=
  { μ := S.μ
    J := J
    transform := S.transform
    weight_nonneg := by
      intro t
      -- rewrite `w` into `weightOfJ` and reuse `w_nonneg`
      simpa [hw] using (S.w_nonneg t)
    memL2 := by
      intro f
      -- rewrite the weight under the sqrt
      simpa [hw] using (S.memL2 f)
    identity_integral := by
      intro f g
      -- rewrite the weight in the integral
      simpa [hw] using (S.identity_integral f g) }

/--
Algebra: `√w · (√w · z) = w · z` as complex scalars (using `w ≥ 0`).

This is a tiny local helper used to absorb weights into the transform.
-/
private lemma sqrt_mul_sqrt_mul {w : ℝ} (hw : 0 ≤ w) (z : ℂ) :
    ((Real.sqrt w : ℝ) : ℂ) * (((Real.sqrt w : ℝ) : ℂ) * z) = ((w : ℝ) : ℂ) * z := by
  have hsqrt : (Real.sqrt w) * (Real.sqrt w) = w := Real.mul_self_sqrt hw
  have hsqrtC :
      (((Real.sqrt w : ℝ) : ℂ) * ((Real.sqrt w : ℝ) : ℂ)) = ((w : ℝ) : ℂ) := by
    simpa using congrArg (fun r : ℝ => (r : ℂ)) hsqrt
  calc
    ((Real.sqrt w : ℝ) : ℂ) * (((Real.sqrt w : ℝ) : ℂ) * z)
        = (((Real.sqrt w : ℝ) : ℂ) * ((Real.sqrt w : ℝ) : ℂ)) * z := by
            simpa [mul_assoc] using
              (mul_assoc (((Real.sqrt w : ℝ) : ℂ)) (((Real.sqrt w : ℝ) : ℂ)) z).symm
    _   = ((w : ℝ) : ℂ) * z := by
            simpa [hsqrtC]

/-- Weighted transform `f ↦ √w · (transform f)`. -/
def weightedTransform : F →ₗ[ℂ] (ℝ → ℂ) where
  toFun f := fun t : ℝ => ((Real.sqrt (S.w t) : ℝ) : ℂ) * S.transform f t
  map_add' f g := by
    funext t
    simp [mul_add]
  map_smul' c f := by
    funext t
    -- scalar multiplication on functions is pointwise; on `ℂ` it is multiplication
    simp [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]

/--
Convert a weighted sesquilinear spectral-measure identity into a **measure-first** identity by
absorbing `√w` into the boundary transform.

This makes `SpectralMeasureSesqIntegralIdentity` a one-step “drop-in” target for the existing Route 3
Hilbert-realization pipeline.
-/
def toSesqMeasureIntegralIdentity :
    HilbertRealization.SesqMeasureIntegralIdentity (F := F) (L := L) :=
  { μ := S.μ
    transform := weightedTransform (L := L) S
    memL2 := by
      intro f
      -- `memL2` is exactly the weighted-transform admissibility hypothesis.
      simpa [weightedTransform] using (S.memL2 f)
    identity_integral := by
      intro f g
      -- Start from the weighted integral identity, then absorb `√w` into the transform.
      have h := S.identity_integral f g
      refine h.trans ?_
      -- Replace integrands by AE equality.
      refine MeasureTheory.integral_congr_ae ?_
      refine Filter.Eventually.of_forall (fun t => ?_)
      have hw0 : 0 ≤ S.w t := S.w_nonneg t
      let a : ℂ := ((Real.sqrt (S.w t) : ℝ) : ℂ)
      let z : ℂ := (starRingEnd ℂ (S.transform f t)) * (S.transform g t)
      have hpoint :
          (starRingEnd ℂ (a * S.transform f t)) * (a * S.transform g t) =
            ((S.w t : ℝ) : ℂ) * z := by
        calc
          (starRingEnd ℂ (a * S.transform f t)) * (a * S.transform g t)
              = (a * (starRingEnd ℂ (S.transform f t))) * (a * S.transform g t) := by
                  simp [a]
          _   = a * (a * z) := by
                  -- commutative reassociation of factors
                  simp [a, z, mul_assoc, mul_left_comm, mul_comm]
          _   = ((S.w t : ℝ) : ℂ) * z := by
                  simpa [a] using (sqrt_mul_sqrt_mul (w := S.w t) hw0 z)
      -- The new integrand is exactly `conj(weightedTransform f) * weightedTransform g`.
      simpa [weightedTransform, a, z] using hpoint.symm }

/--
**Drop-in Route 3 target:** a spectral-measure-form weighted identity immediately yields a
`ReflectionPositivityRealization` via the existing `HilbertRealization` pipeline.
-/
theorem reflectionPositivityRealization :
    OptionalTargets.ReflectionPositivityRealization (F := F) (L := L) := by
  classical
  -- Convert to a measure-first Bochner identity, then reuse the existing lemma.
  exact
    HilbertRealization.SesqMeasureIntegralIdentity.reflectionPositivityRealization (F := F) (L := L)
      (toSesqMeasureIntegralIdentity (F := F) (L := L) S)

/-- A spectral-measure-form identity yields the Route 3 Weil gate `WeilGate`. -/
theorem WeilGate : L.WeilGate :=
  OptionalTargets.WeilGate_of_reflectionPositivityRealization (F := F) (L := L)
    (h := reflectionPositivityRealization (F := F) (L := L) S)

/-- **End-to-end entrypoint:** a spectral-measure-form identity yields `RiemannHypothesis`. -/
theorem RH : RiemannHypothesis :=
  LagariasFramework.WeilGate_implies_RH (L := L) (WeilGate (F := F) (L := L) S)

end SpectralMeasureSesqIntegralIdentity

end Sesquilinear

/-! ## Operator-form identity (quadratic form) -/

/-- An operator-form representation of the Route-3 quadratic form.

This matches the “Weil sum = ⟪A v, v⟫” picture that appears in operator/spectral-measure papers. -/
structure OperatorQuadraticIdentity (L : LagariasFramework F) where
  /-- The Hilbert space in which the quadratic form lives. -/
  H : Type
  instNACG : NormedAddCommGroup H
  instIP : InnerProductSpace ℂ H
  instComplete : CompleteSpace H
  /-- Linear map sending test functions into the Hilbert space. -/
  T : F →ₗ[ℂ] H
  /-- A bounded operator generating the quadratic form. -/
  A : H →L[ℂ] H
  /-- Self-adjointness (so the quadratic form is real-valued). -/
  selfAdjoint : IsSelfAdjoint A
  /-- The quadratic-form identity (real-part form, matching `WeilGate`). -/
  identity_re :
    ∀ f : F, (L.W1 (TestSpace.quad (F := F) f)).re = (⟪A (T f), T f⟫_ℂ).re

namespace OperatorQuadraticIdentity

variable {F : Type} [TestSpace F] (L : LagariasFramework F) (O : OperatorQuadraticIdentity (F := F) (L := L))

-- Register instances locally when using `O`.
attribute [instance] OperatorQuadraticIdentity.instNACG
attribute [instance] OperatorQuadraticIdentity.instIP
attribute [instance] OperatorQuadraticIdentity.instComplete

end OperatorQuadraticIdentity

/-! ## Spectral-measure-form identity (quadratic form) -/

/-- A spectral-measure-form representation of the Route-3 quadratic form.

This is closer to `SpectralIdentity` but does not insist the weight comes from a `J`-field.
Instead it packages a general measurable weight `w : ℝ → ℝ`.

If one can identify `w = weightOfJ J` and `transform = mellinOnCriticalLine`, this becomes
exactly the PSC splice target in `HilbertRealization.lean`. -/
structure SpectralMeasureQuadraticIdentity (L : LagariasFramework F) where
  /-- A measure on the spectral parameter. -/
  μ : Measure ℝ := volume
  /-- A nonnegative weight function (typically the spectral variable or a derived density). -/
  w : ℝ → ℝ
  w_nonneg : ∀ t : ℝ, 0 ≤ w t
  /-- Boundary/spectral transform. -/
  transform : F → ℝ → ℂ := mellinOnCriticalLine
  measurable_transform : ∀ f : F, Measurable (transform f)
  integrable_energy : ∀ f : F, Integrable (fun t : ℝ => w t * Complex.normSq (transform f t)) μ
  /-- Quadratic form identity as a real integral. -/
  identity_re :
    ∀ f : F,
      (L.W1 (TestSpace.quad (F := F) f)).re =
        ∫ t : ℝ, (w t) * Complex.normSq (transform f t) ∂ μ

namespace SpectralMeasureQuadraticIdentity

variable {F : Type} [TestSpace F] (L : LagariasFramework F) (S : SpectralMeasureQuadraticIdentity (F := F) (L := L))

/-- If you additionally supply a `J` whose weight matches `w`, you get the canonical `SpectralIdentity`. -/
def toSpectralIdentity
    (J : ℂ → ℂ) (hw : ∀ t : ℝ, S.w t = HilbertRealization.weightOfJ J t) :
    HilbertRealization.SpectralIdentity (F := F) (L := L) :=
  { μ := S.μ
    J := J
    transform := S.transform
    measurable_transform := S.measurable_transform
    integrable_energy := by
      intro f
      -- rewrite `w` into `weightOfJ` and reuse `integrable_energy`
      simpa [hw] using (S.integrable_energy f)
    identity_re := by
      intro f
      -- rewrite the RHS weight and reuse `identity_re`
      simpa [hw] using (S.identity_re f) }

end SpectralMeasureQuadraticIdentity

end ExplicitFormula
end RiemannRecognitionGeometry
