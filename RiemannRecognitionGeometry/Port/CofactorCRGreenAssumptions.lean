/-!
# Port step: make the cofactor CR/Green requirement explicitly energy-based

The remaining “real work” item in the port plan is to prove a **faithful**
CR/Green estimate that converts a Carleson-box energy bound into a bound on the
cofactor phase change:

`Ebox ρ I ≤ E·|I|  ⇒  ‖Δ phase_cofactor‖ ≤ C_geom·√(E·|I|)·|I|^{-1/2}`.

This file packages that target as a dedicated hypothesis bundle
`Port.CofactorCRGreenAssumptions`. This is *strictly closer* to the Hardy/Dirichlet
blueprint than the older `ClassicalAnalysisAssumptions.cofactor_green_identity_axiom_statement`,
because the energy functional appears explicitly.

For now, we also provide a compatibility lemma:
the existing project-level cofactor Green bound implies the energy-based statement
(trivially, since it does not actually depend on the energy functional yet).
-/

import RiemannRecognitionGeometry.Assumptions
import RiemannRecognitionGeometry.Port.CofactorEnergy
import RiemannRecognitionGeometry.Port.HardyDirichletCRGreen

noncomputable section

namespace RiemannRecognitionGeometry
namespace Port

open Real Complex

/-- **Energy-based cofactor CR/Green target** for the concrete energy functional
`Ebox := cofactorEbox_poisson`.

This is the exact “Green pairing + Cauchy–Schwarz + window-energy cancellation” step we ultimately
want to justify (or prove) inside this repo. -/
structure CofactorCRGreenAssumptions : Prop where
  cofactor_green_from_energy :
    ∀ (I : WhitneyInterval) (ρ : ℂ) (E : ℝ),
      0 < E →
      cofactorEbox_poisson ρ I ≤ E * (2 * I.len) →
      ‖rgCofactorPhaseAngle ρ (I.t0 + I.len) - rgCofactorPhaseAngle ρ (I.t0 - I.len)‖ ≤
        C_geom * Real.sqrt (E * (2 * I.len)) * (1 / Real.sqrt (2 * I.len))

/-- The energy-based assumption discharges the generic Hardy/Dirichlet CRGreen interface
for `Ebox := cofactorEbox_poisson`. -/
theorem hardyDirichletCRGreen_of_cofactorCRGreenAssumptions
    (h : CofactorCRGreenAssumptions) :
    HardyDirichletCRGreen cofactorEbox_poisson := by
  refine ⟨?_⟩
  intro I ρ E hE_pos hEbox
  exact h.cofactor_green_from_energy I ρ E hE_pos hEbox

/-- Compatibility: the current project-level cofactor Green bound implies the energy-based
cofactor CR/Green target (the implication is currently non-faithful, but keeps the build usable
until the true Green pairing proof is ported). -/
theorem cofactorCRGreenAssumptions_of_ClassicalAnalysisAssumptions
    (hCA : ClassicalAnalysisAssumptions) :
    CofactorCRGreenAssumptions := by
  refine ⟨?_⟩
  intro I ρ E hE_pos _hEbox
  -- Use the existing cofactor Green bound with `C := E` and `E := E`.
  simpa using
    (hCA.cofactor_green_identity_axiom_statement I ρ E hE_pos E hE_pos (le_rfl : E ≤ E))

end Port
end RiemannRecognitionGeometry
