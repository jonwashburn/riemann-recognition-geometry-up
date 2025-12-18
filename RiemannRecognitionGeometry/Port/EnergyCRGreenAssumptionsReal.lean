/-
# Port step: bundle the **real-valued** CR/Green targets (blueprint-style)

`Port.RealPhaseTransfer` introduces the real-valued CR/Green targets:

- `XiCRGreenAssumptionsReal` (for `actualPhaseSignal`), and
- `CofactorCRGreenAssumptionsReal` (for `rgCofactorPhaseReal`).

This file bundles them into a single record, mirroring `Port.EnergyCRGreenAssumptions`
on the `Real.Angle` side.
-/

import RiemannRecognitionGeometry.Port.RealPhaseTransfer
import RiemannRecognitionGeometry.Port.EnergyCRGreenAssumptions

noncomputable section

namespace RiemannRecognitionGeometry
namespace Port

/-- Bundled **real-valued** CR/Green targets (xi-side + cofactor-side). -/
structure EnergyCRGreenAssumptionsReal : Prop where
  xi : XiCRGreenAssumptionsReal
  cofactor : CofactorCRGreenAssumptionsReal

/-- A bundled real-valued CR/Green certificate implies the bundled `Real.Angle` energy-based one. -/
theorem energyCRGreenAssumptions_of_real (h : EnergyCRGreenAssumptionsReal) :
    EnergyCRGreenAssumptions := by
  refine ⟨?_, ?_⟩
  · exact xiCRGreenAssumptions_of_real h.xi
  · exact cofactorCRGreenAssumptions_of_real h.cofactor

end Port
end RiemannRecognitionGeometry
