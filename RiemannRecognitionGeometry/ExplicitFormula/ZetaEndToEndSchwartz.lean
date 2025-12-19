import RiemannRecognitionGeometry.ExplicitFormula.ZetaInstantiation
import RiemannRecognitionGeometry.ExplicitFormula.PSCSplice
import RiemannRecognitionGeometry.ExplicitFormula.ZetaRightEdgePhaseLimit
import RiemannRecognitionGeometry.ExplicitFormula.BoundaryWedgeInterfaces

/-!
# Route 3: end-to-end ζ run (Route 3 test space)

This file is a wiring/sanity target:

Given
- a concrete `LagariasContourFramework` on Route‑3’s fixed test space `Route3.F`,
- ζ PSC-components (`PSCComponents_zeta`), and
- the remaining contour-to-boundary analytic hypotheses packaged as
  `RightEdgePhaseLimitAssumptions`,

we can fire the existing Route‑3 pipeline and obtain `RiemannHypothesis`.

No new analytic theorems are proved here; everything is assumptions → wiring.
-/

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula
namespace ZetaInstantiation

open MeasureTheory Complex

namespace EndToEnd

/-!
## End-to-end: `RightEdgePhaseLimitAssumptions` → RH
-/

variable [TestSpace Route3.F]

/-- All remaining hypotheses needed to run the ζ chain to `RiemannHypothesis` on `Route3.F`. -/
structure Assumptions where
  LC : LagariasContourFramework Route3.F
  H : ZetaPSCHypotheses
  Aphase :
    ExplicitFormulaCancellationSkeleton.RightEdgePhaseLimitAssumptions
      (LC := LC) (P := (PSCComponents_zeta H))
  /-- The shared “transform / L² / integrability” bundle (factored in `ZetaInstantiation`). -/
  Azeta : Assumptions_zeta (LC := LC) (H := H)

theorem RH (A : Assumptions) : RiemannHypothesis := by
  classical

  -- 1) Get `explicit_formula_cancellation_contour` for all `h` from the right-edge limit bundle.
  have hContour :
      ∀ h : Route3.F,
        ContourToBoundary.explicit_formula_cancellation_contour
          (LC := A.LC) (P := PSCComponents_zeta A.H) h := by
    intro h
    exact
      ExplicitFormulaCancellationSkeleton.explicit_formula_cancellation_contour_of_rightEdgePhaseLimitAssumptions
        (LC := A.LC) (P := PSCComponents_zeta A.H) A.Aphase h

  -- 2) Convert contour cancellation into the `explicit_formula_cancellation` hypothesis PSCSplice expects.
  have hExplicit :
      ∀ f g : Route3.F,
        ContourToBoundary.explicit_formula_cancellation
          (L := A.LC.L) (P := PSCComponents_zeta A.H) (h := pair (F := Route3.F) f g) := by
    intro f g
    exact
      ContourToBoundary.explicit_formula_cancellation_of_contour
        (LC := A.LC) (P := PSCComponents_zeta A.H) (h := pair (F := Route3.F) f g)
        (hContour (pair (F := Route3.F) f g))

  -- 3) Fire the Route‑3 pipeline.
  exact
    Route3.PSCSplice.RH_ofContourToBoundary
      (P := PSCComponents_zeta A.H)
      (L := A.LC.L)
      (transform := A.Azeta.transform)
      (transform_eq_mellinOnCriticalLine := A.Azeta.transform_eq_mellinOnCriticalLine)
      (memL2 := by
        intro f
        -- `((PSCComponents_zeta A.H).μ_spec)` is definitionally `A.H.μ_spec`.
        simpa using (A.Azeta.memL2 f))
      (h_explicit := hExplicit)
      (h_integrable_F := A.Azeta.integrable_pairTransform_volume)
      (h_integrable_vol := A.Azeta.integrable_pairTransform_deriv_volume)
      (h_integrable_μ := A.Azeta.integrable_pairTransform_μ)

/--
Variant assumptions where the right-edge input is provided in the more structural form:

- horizontal vanishing (`horizBottom_vanish`, `horizTop_vanish`),
- plus `RightEdgeIntegralIdentityAssumptions` (integrability + full-line integral identity),

from which `RightEdgePhaseLimitAssumptions` is derived automatically.
-/
structure AssumptionsIntegralId where
  LC : LagariasContourFramework Route3.F
  H : ZetaPSCHypotheses
  /-- Identify the contour framework xi with `xiLagarias`. -/
  xiLC : LC.xi = xiLagarias
  /-- Horizontal edges vanish (all test functions). -/
  horizBottom_vanish :
    ∀ h : Route3.F,
      Filter.Tendsto
        (fun T : ℝ =>
          ContourW1.horizBottom (fun s : ℂ => M[h](s) * logDeriv LC.xi s) LC.c T)
        Filter.atTop (nhds 0)
  horizTop_vanish :
    ∀ h : Route3.F,
      Filter.Tendsto
        (fun T : ℝ =>
          ContourW1.horizTop (fun s : ℂ => M[h](s) * logDeriv LC.xi s) LC.c T)
        Filter.atTop (nhds 0)
  /-- Integrability + full-line integral identity (the key remaining analytic content). -/
  rightEdgeIntegralId :
    ExplicitFormulaCancellationSkeleton.RightEdgeIntegralIdentityAssumptions
      (LC := LC) (P := PSCComponents_zeta H)
  /-- The shared “transform / L² / integrability” bundle (factored in `ZetaInstantiation`). -/
  Azeta : Assumptions_zeta (LC := LC) (H := H)

def AssumptionsIntegralId.toAssumptions (A : AssumptionsIntegralId) : Assumptions where
  LC := A.LC
  H := A.H
  Aphase :=
    ZetaInstantiation.EndToEnd.rightEdgePhaseLimitAssumptions_zeta_of_rightEdgeIntegralIdentityAssumptions
      (LC := A.LC) (H := A.H)
      (hxiLC := A.xiLC)
      (hBot := A.horizBottom_vanish)
      (hTop := A.horizTop_vanish)
      (AId := A.rightEdgeIntegralId)
  Azeta := A.Azeta

theorem RH_of_integralId (A : AssumptionsIntegralId) : RiemannHypothesis :=
  RH (A := A.toAssumptions)

/-!
## End-to-end: boundary wedge + splice identity → RH

This is the “single bundle” entrypoint for the PSC/Route‑3 ζ run: we package the boundary‑wedge
interface (hence (P+)) together with the Route‑3 measure‑first splice identity assumptions.

No new analysis is proved here; we just expose the fully bundled hypothesis surface.
-/

variable [TestSpace Route3.F]

/-- One-stop assumption bundle for an end-to-end ζ run using the Route‑3 splice identity. -/
structure AssumptionsSplice where
  /-- ζ boundary hypotheses (phase representation, phase–velocity, etc.). -/
  H : ZetaPSCHypotheses
  /-- Boundary wedge interface, implying (P+) / cosine nonnegativity for `H.boundaryPhase`. -/
  wedge : BoundaryWedgeAssumptions H
  /-- Route‑3 measure-first splice identity (against a positive measure). -/
  splice : Route3.PSCSplice.Assumptions (F := Route3.F)

/-- Convenience: the wedge assumptions imply `(P+)` for the ζ pinch field. -/
theorem AssumptionsSplice.PPlus_zeta (A : AssumptionsSplice) : PPlus_zeta :=
  PPlus_zeta_of_boundary_wedge A.H A.wedge

/-- Convenience: the wedge assumptions imply the phase-positivity target `cos(θ) ≥ 0` a.e. -/
theorem AssumptionsSplice.boundaryPhase_cos_nonneg_ae (A : AssumptionsSplice) :
    (∀ᵐ t : ℝ, 0 ≤ Real.cos (A.H.boundaryPhase t)) :=
  boundaryPhase_cos_nonneg_ae_of_boundary_wedge A.H A.wedge

/-- If the Route‑3 splice identity holds (packaged together with the boundary wedge), then RH follows. -/
theorem RH_of_splice (A : AssumptionsSplice) : RiemannHypothesis :=
  Route3.PSCSplice.RHμ_spec (A := A.splice)

end EndToEnd

end ZetaInstantiation
end ExplicitFormula
end RiemannRecognitionGeometry
