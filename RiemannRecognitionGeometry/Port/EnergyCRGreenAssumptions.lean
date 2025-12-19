/-
# Port step: bundle the explicit energy-based CR/Green targets

We now have two explicit (energy-based) CR/Green targets in the Port layer:

- `Port.XiCRGreenAssumptions`: upper bound on `totalPhaseSignal` from `xiEbox_poisson`,
- `Port.CofactorCRGreenAssumptions`: lower/tail route bound from `cofactorEbox_poisson`.

This file just bundles them into one small record so downstream “Port main” theorems can take a
single assumption argument, instead of two separate ones.
-/

import RiemannRecognitionGeometry.Port.CofactorCRGreenAssumptions
import RiemannRecognitionGeometry.Port.XiCRGreenAssumptions

noncomputable section

namespace RiemannRecognitionGeometry
namespace Port

/-- Bundled energy-based CR/Green targets (xi-side + cofactor-side). -/
structure EnergyCRGreenAssumptions : Prop where
  xi : XiCRGreenAssumptions
  cofactor : CofactorCRGreenAssumptions

/-- Bundled **strong** energy-form CR/Green targets (xi-side + cofactor-side). -/
structure EnergyCRGreenAssumptionsStrong : Prop where
  xi : XiCRGreenAssumptionsStrong
  cofactor : CofactorCRGreenAssumptionsStrong

/-- Strong CR/Green bundle ⇒ the weaker bundle (by strong→weak on each side). -/
theorem energyCRGreenAssumptions_of_strong (h : EnergyCRGreenAssumptionsStrong) :
    EnergyCRGreenAssumptions := by
  refine ⟨?_, ?_⟩
  · exact xiCRGreenAssumptions_of_xiCRGreenAssumptionsStrong h.xi
  · exact cofactorCRGreenAssumptions_of_cofactorCRGreenAssumptionsStrong h.cofactor

/-- Compatibility: the current project-level `ClassicalAnalysisAssumptions` implies the bundled
energy-based CR/Green targets (non-faithfully, until a true Green pairing proof lands). -/
theorem energyCRGreenAssumptions_of_ClassicalAnalysisAssumptions
    (hCA : ClassicalAnalysisAssumptions) :
    EnergyCRGreenAssumptions := by
  refine ⟨?_, ?_⟩
  · exact xiCRGreenAssumptions_of_ClassicalAnalysisAssumptions hCA
  · exact cofactorCRGreenAssumptions_of_ClassicalAnalysisAssumptions hCA

end Port
end RiemannRecognitionGeometry
