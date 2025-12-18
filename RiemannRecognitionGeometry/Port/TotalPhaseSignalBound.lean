/-
# Port step: energy-based upper bound on `totalPhaseSignal`

This is the “upper bound” analogue of `Port/CofactorTailBound.lean`:

- use the existing Fefferman–Stein axiom `PoissonExtension.bmo_carleson_embedding` to get
  an energy bound for `xiEbox_poisson I`, then
- apply the energy-based CR/Green target `Port.XiCRGreenAssumptions` to bound `xiPhaseChange I`,
- and finally use the √|I| cancellation to get a uniform `U_tail M` bound.

This lets the Port contradiction chain avoid the older non-faithful interface
`ClassicalAnalysisAssumptions.green_identity_axiom_statement`.
-/

import RiemannRecognitionGeometry.Axioms
import RiemannRecognitionGeometry.CarlesonBound
import RiemannRecognitionGeometry.Port.CofactorCarlesonBudget
import RiemannRecognitionGeometry.Port.XiCarlesonBudget
import RiemannRecognitionGeometry.Port.XiCRGreenAssumptions

noncomputable section

namespace RiemannRecognitionGeometry
namespace Port

open Real MeasureTheory Set

/-- Energy-based Port analogue of `Axioms.totalPhaseSignal_bound`. -/
theorem totalPhaseSignal_bound_of_xiCRGreenAssumptions (I : WhitneyInterval)
    (hXi : XiCRGreenAssumptions)
    (M : ℝ) (h_osc : InBMOWithBound logAbsXi M) :
    totalPhaseSignal I ≤ U_tail M := by
  -- Rewrite `totalPhaseSignal` as `xiPhaseChange`.
  unfold totalPhaseSignal

  -- 1) BMO hypothesis in the exact shape required by `PoissonExtension.bmo_carleson_embedding`.
  have h_bmo' :
      ∀ a b : ℝ, a < b →
        (b - a)⁻¹ * ∫ t in Icc a b, |logAbsXi t - (b - a)⁻¹ * ∫ s in Icc a b, logAbsXi s| ≤ M :=
    poissonExtension_bmoHyp_of_InBMOWithBound (w := logAbsXi) h_osc

  -- 2) Fefferman–Stein (axiom): energy ≤ C_FS * M^2 * |I|.
  have h_embed :=
    PoissonExtension.bmo_carleson_embedding
      (w := logAbsXi)
      (a := I.t0 - I.len) (b := I.t0 + I.len)
      (M := M) h_osc.1 h_bmo'

  have h_ba : (I.t0 + I.len) - (I.t0 - I.len) = 2 * I.len := by ring
  have h_energy :
      xiEbox_poisson I ≤ K_tail M * (2 * I.len) := by
    -- `xiEbox_poisson I` is definitionally the same `carleson_energy` on these endpoints.
    simpa [xiEbox_poisson, K_tail, h_ba] using h_embed

  -- 3) CR/Green: convert energy bound into a phase bound at the correct scale.
  have hK_pos : 0 < K_tail M := K_tail_pos h_osc.1
  have h_phase :
      xiPhaseChange I ≤
        C_geom * Real.sqrt (K_tail M * (2 * I.len)) * (1 / Real.sqrt (2 * I.len)) :=
    hXi.xi_green_from_energy I (K_tail M) hK_pos h_energy

  -- 4) Cancel √|I| and rewrite to `U_tail M`.
  have h_len_pos : 0 < (2 * I.len) := by nlinarith [I.len_pos]
  have hK_nonneg : 0 ≤ K_tail M := K_tail_nonneg M
  have h_cancel :
      Real.sqrt (K_tail M * (2 * I.len)) * (1 / Real.sqrt (2 * I.len)) = Real.sqrt (K_tail M) := by
    simpa using (sqrt_energy_cancellation (K_tail M) (2 * I.len) hK_nonneg h_len_pos)
  have h_phase' : xiPhaseChange I ≤ C_geom * Real.sqrt (K_tail M) := by
    have h := h_phase
    -- reassociate to rewrite the cancellation factor
    rw [mul_assoc] at h
    rw [h_cancel] at h
    exact h

  -- Conclude.
  simpa [U_tail] using h_phase'

/-- Variant: derive the same upper bound from the **Hardy/Dirichlet Carleson-budget interface**
for `xiEbox_poisson` (and the xi CR/Green target), in the “interval contains a zero” setting.

This matches the blueprint decomposition “Carleson budget + CR/Green ⇒ phase bound”, but is only
useful when one already has a zero `ρ` with `Im ρ ∈ I`. -/
theorem totalPhaseSignal_bound_of_hardyDirichletCarlesonBudget_xiEbox_poisson
    (hCar : HardyDirichletCarlesonBudget xiEbox_poissonEbox)
    (hXi : XiCRGreenAssumptions)
    (I : WhitneyInterval) (ρ : ℂ)
    (hρ_zero : completedRiemannZeta ρ = 0) (hρ_im : ρ.im ∈ I.interval)
    (M : ℝ) (h_osc : InBMOWithBound logAbsXi M) :
    totalPhaseSignal I ≤ U_tail M := by
  -- Rewrite `totalPhaseSignal` as `xiPhaseChange`.
  unfold totalPhaseSignal

  -- Carleson budget: energy ≤ K_tail(M)·|I| (interface requires the “zero in interval” data).
  have h_bmo : InBMOWithBound (cofactorLogAbs ρ) M := by
    simpa [cofactorLogAbs] using h_osc
  have h_energy : xiEbox_poisson I ≤ K_tail M * (2 * I.len) := by
    simpa [xiEbox_poissonEbox] using hCar.cofactor_boxEnergy_le I ρ M h_bmo hρ_zero hρ_im

  -- CR/Green: convert energy bound into a phase bound at the correct scale.
  have hK_pos : 0 < K_tail M := K_tail_pos h_osc.1
  have h_phase :
      xiPhaseChange I ≤
        C_geom * Real.sqrt (K_tail M * (2 * I.len)) * (1 / Real.sqrt (2 * I.len)) :=
    hXi.xi_green_from_energy I (K_tail M) hK_pos h_energy

  -- Cancel √|I| and rewrite to `U_tail M`.
  have h_len_pos : 0 < (2 * I.len) := by nlinarith [I.len_pos]
  have hK_nonneg : 0 ≤ K_tail M := K_tail_nonneg M
  have h_cancel :
      Real.sqrt (K_tail M * (2 * I.len)) * (1 / Real.sqrt (2 * I.len)) = Real.sqrt (K_tail M) := by
    simpa using (sqrt_energy_cancellation (K_tail M) (2 * I.len) hK_nonneg h_len_pos)

  have h_phase' : xiPhaseChange I ≤ C_geom * Real.sqrt (K_tail M) := by
    have h := h_phase
    rw [mul_assoc] at h
    rw [h_cancel] at h
    exact h

  simpa [U_tail] using h_phase'

end Port
end RiemannRecognitionGeometry
