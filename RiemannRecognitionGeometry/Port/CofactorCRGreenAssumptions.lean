/-
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
import RiemannRecognitionGeometry.Port.CofactorCarlesonBudget
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

/-- **Strong energy-form cofactor CR/Green target** for `Ebox := cofactorEbox_poisson`.

This is the cleanest “faithful” statement: it bounds phase change directly by `sqrt(Ebox)`. -/
structure CofactorCRGreenAssumptionsStrong : Prop where
  cofactor_green_from_energy_strong :
    ∀ (I : WhitneyInterval) (ρ : ℂ),
      ‖rgCofactorPhaseAngle ρ (I.t0 + I.len) - rgCofactorPhaseAngle ρ (I.t0 - I.len)‖ ≤
        C_geom * Real.sqrt (cofactorEbox_poisson ρ I) * (1 / Real.sqrt (2 * I.len))

/-- Strong energy-form cofactor CR/Green bound ⇒ the weaker API that quantifies over an auxiliary
energy density parameter `E`. -/
theorem cofactorCRGreenAssumptions_of_cofactorCRGreenAssumptionsStrong
    (h : CofactorCRGreenAssumptionsStrong) :
    CofactorCRGreenAssumptions := by
  refine ⟨?_⟩
  intro I ρ E hE_pos hEbox
  have h0 :=
    h.cofactor_green_from_energy_strong I ρ
  -- From `Ebox ≤ E·|I|`, we get `√Ebox ≤ √(E·|I|)`.
  have hsqrt_le : Real.sqrt (cofactorEbox_poisson ρ I) ≤ Real.sqrt (E * (2 * I.len)) := by
    exact Real.sqrt_le_sqrt hEbox
  -- `C_geom` and `1/√(2*I.len)` are nonnegative.
  have hC_nonneg : 0 ≤ (C_geom : ℝ) := by
    simp [RiemannRecognitionGeometry.C_geom]
  have hden_nonneg : 0 ≤ (1 / Real.sqrt (2 * I.len) : ℝ) :=
    one_div_nonneg.mpr (Real.sqrt_nonneg _)
  -- Replace `√Ebox` by the larger `√(E·|I|)` on the RHS.
  have :
      C_geom * Real.sqrt (cofactorEbox_poisson ρ I) * (1 / Real.sqrt (2 * I.len))
        ≤ C_geom * Real.sqrt (E * (2 * I.len)) * (1 / Real.sqrt (2 * I.len)) := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt_le hC_nonneg) hden_nonneg
  exact le_trans h0 this

/-- The energy-based assumption discharges the generic Hardy/Dirichlet CRGreen interface
for `Ebox := cofactorEbox_poisson`. -/
theorem hardyDirichletCRGreen_of_cofactorCRGreenAssumptions
    (h : CofactorCRGreenAssumptions) :
    HardyDirichletCRGreen cofactorEbox_poisson := by
  refine ⟨?_⟩
  intro I ρ E hE_pos hEbox
  exact h.cofactor_green_from_energy I ρ E hE_pos hEbox

/-- The **strong** energy-form cofactor CR/Green assumption discharges the generic
`HardyDirichletCRGreenStrong` interface for `Ebox := cofactorEbox_poisson`. -/
theorem hardyDirichletCRGreenStrong_of_cofactorCRGreenAssumptionsStrong
    (h : CofactorCRGreenAssumptionsStrong) :
    HardyDirichletCRGreenStrong cofactorEbox_poisson := by
  refine ⟨?_, ?_⟩
  · intro ρ I
    -- energy ≥ 0
    simpa [cofactorEbox_poisson] using
      poissonExtension_carleson_energy_nonneg (w := cofactorLogAbs ρ) (a := I.t0 - I.len) (b := I.t0 + I.len)
  · intro I ρ
    exact h.cofactor_green_from_energy_strong I ρ

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
