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

/-- **Strong energy-form xi CR/Green target** for `Ebox := xiEbox_poisson`.

This is the faithful “energy form” statement: it bounds phase change directly by `sqrt(Ebox)`. -/
structure XiCRGreenAssumptionsStrong : Prop where
  xi_green_from_energy_strong :
    ∀ (I : WhitneyInterval),
      xiPhaseChange I ≤
        C_geom * Real.sqrt (xiEbox_poisson I) * (1 / Real.sqrt (2 * I.len))

/-- Strong energy-form xi CR/Green bound ⇒ the weaker API that quantifies over an auxiliary
energy density parameter `E`. -/
theorem xiCRGreenAssumptions_of_xiCRGreenAssumptionsStrong
    (h : XiCRGreenAssumptionsStrong) :
    XiCRGreenAssumptions := by
  refine ⟨?_⟩
  intro I E hE_pos hEbox
  have h0 :=
    h.xi_green_from_energy_strong I
  -- From `Ebox ≤ E·|I|`, we get `√Ebox ≤ √(E·|I|)`.
  have hsqrt_le : Real.sqrt (xiEbox_poisson I) ≤ Real.sqrt (E * (2 * I.len)) := by
    exact Real.sqrt_le_sqrt hEbox
  -- `C_geom` and `1/√(2*I.len)` are nonnegative.
  have hC_nonneg : 0 ≤ (C_geom : ℝ) := by
    simp [RiemannRecognitionGeometry.C_geom]
  have hden_nonneg : 0 ≤ (1 / Real.sqrt (2 * I.len) : ℝ) :=
    one_div_nonneg.mpr (Real.sqrt_nonneg _)
  -- Replace `√Ebox` by the larger `√(E·|I|)` on the RHS.
  have :
      C_geom * Real.sqrt (xiEbox_poisson I) * (1 / Real.sqrt (2 * I.len))
        ≤ C_geom * Real.sqrt (E * (2 * I.len)) * (1 / Real.sqrt (2 * I.len)) := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt_le hC_nonneg) hden_nonneg
  exact le_trans h0 this

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
