/-
# Port step: make the **xi phase** CR/Green requirement explicitly energy-based

The existing RG proof uses `ClassicalAnalysisAssumptions.green_identity_axiom_statement` to bound
`totalPhaseSignal I = xiPhaseChange I`.

That interface is not faithful (it does not mention an energy functional), so in the Port layer we
introduce an explicit target:

`xiEbox_poisson I ≤ E·|I|  ⇒  xiPhaseChange I ≤ C_geom·√(E·|I|)·|I|^{-1/2}`.

This is the “upper-bound analogue” of `Port.CofactorCRGreenAssumptions`.
-/

import RiemannRecognitionGeometry.Assumptions
import RiemannRecognitionGeometry.Port.XiEnergy

noncomputable section

namespace RiemannRecognitionGeometry
namespace Port

open Real

/-- **Energy-based xi CR/Green target** for the concrete energy functional `xiEbox_poisson`. -/
structure XiCRGreenAssumptions : Prop where
  xi_green_from_energy :
    ∀ (I : WhitneyInterval) (E : ℝ),
      0 < E →
      xiEbox_poisson I ≤ E * (2 * I.len) →
      xiPhaseChange I ≤
        C_geom * Real.sqrt (E * (2 * I.len)) * (1 / Real.sqrt (2 * I.len))

/-- Compatibility: the current project-level `ClassicalAnalysisAssumptions` implies the energy-based
xi CR/Green target (non-faithfully, since it ignores the energy functional for now). -/
theorem xiCRGreenAssumptions_of_ClassicalAnalysisAssumptions
    (hCA : ClassicalAnalysisAssumptions) :
    XiCRGreenAssumptions := by
  refine ⟨?_⟩
  intro I E hE_pos _hEbox
  -- Use the existing Green bound with `C := E` and `E := E`.
  simpa using
    (hCA.green_identity_axiom_statement I E hE_pos E hE_pos (le_rfl : E ≤ E))

end Port
end RiemannRecognitionGeometry
