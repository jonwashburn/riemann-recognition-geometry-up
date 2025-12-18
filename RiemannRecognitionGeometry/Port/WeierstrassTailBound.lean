/-!
# Port step: derive the RG tail bound from Hardy/Dirichlet-style interfaces

This file shows (in Lean) that the *shape* of the RG Weierstrass tail bound

`‖xiPhaseChangeAngle I - blaschke‖ ≤ U_tail M`

is exactly what you get from combining:

- a **Carleson energy budget** (box energy ≤ `K_tail M · |I|`), and
- a **CR/Green** inequality (phase change ≤ `C_geom √(E·|I|) · |I|^{-1/2}`),

plus the standard `√|I|` cancellation.

This mirrors the intent of the disabled `reality` pipeline (Carleson + CRGreen).
No new axioms are introduced: we take the Hardy/Dirichlet statements as explicit hypotheses.
-/

import RiemannRecognitionGeometry.CarlesonBound
import RiemannRecognitionGeometry.Phase
import RiemannRecognitionGeometry.Port.HardyDirichletCarleson
import RiemannRecognitionGeometry.Port.HardyDirichletCRGreen

noncomputable section

namespace RiemannRecognitionGeometry
namespace Port

open Real

/-- **Derived tail bound (from Hardy/Dirichlet-style hypotheses)**.

This is the non-vacuous version of `Conjectures.weierstrass_tail_bound_axiom_statement`:
it requires an actual energy inequality (encoded by `HardyDirichletCarlesonBudget Ebox`), and then
uses `HardyDirichletCRGreen Ebox` to convert that into a phase bound with the correct scaling. -/
theorem weierstrass_tail_bound_of_hardyDirichlet
    (Ebox : ℂ → WhitneyInterval → ℝ)
    (hCar : HardyDirichletCarlesonBudget Ebox)
    (hGreen : HardyDirichletCRGreen Ebox)
    (I : WhitneyInterval) (ρ : ℂ) (M : ℝ) (hM_pos : 0 < M)
    (h_bmo : InBMOWithBound (cofactorLogAbs ρ) M)
    (hρ_zero : completedRiemannZeta ρ = 0) (hρ_im : ρ.im ∈ I.interval) :
    let d : ℝ := ρ.re - 1/2
    let y_hi : ℝ := I.t0 + I.len - ρ.im
    let y_lo : ℝ := I.t0 - I.len - ρ.im
    let blaschke := Real.arctan (y_lo / d) - Real.arctan (y_hi / d)
    ‖xiPhaseChangeAngle I - (blaschke : Real.Angle)‖ ≤ U_tail M := by
  intro d y_hi y_lo blaschke

  -- 1) Reduce to cofactor phase change (pure algebra in `Real.Angle`).
  have h_reduce :
      ‖xiPhaseChangeAngle I - (blaschke : Real.Angle)‖ =
        ‖rgCofactorPhaseAngle ρ (I.t0 + I.len) - rgCofactorPhaseAngle ρ (I.t0 - I.len)‖ := by
    have : (blaschke : Real.Angle) = rgBlaschkePhaseChangeAngle I ρ := by
      simp [rgBlaschkePhaseChangeAngle, rgBlaschkePhaseChange, rgBlaschkePhase,
        d, y_hi, y_lo, blaschke]
    simpa [this] using (norm_xiPhaseChangeAngle_sub_rgBlaschkePhaseChangeAngle I ρ)

  -- 2) Carleson energy budget gives an energy bound at scale `K_tail M · |I|`.
  have h_energy :
      Ebox ρ I ≤ K_tail M * (2 * I.len) :=
    hCar.cofactor_boxEnergy_le I ρ M h_bmo hρ_zero hρ_im

  -- 3) CR/Green converts the energy bound into a cofactor phase bound.
  have hK_pos : 0 < K_tail M := K_tail_pos hM_pos
  have h_cofactor_phase :
      ‖rgCofactorPhaseAngle ρ (I.t0 + I.len) - rgCofactorPhaseAngle ρ (I.t0 - I.len)‖ ≤
        C_geom * Real.sqrt (K_tail M * (2 * I.len)) * (1 / Real.sqrt (2 * I.len)) :=
    hGreen.cofactor_phase_change_bound I ρ (K_tail M) hK_pos h_energy

  -- 4) Cancel `√|I|` and rewrite the RHS as `U_tail M`.
  have h_len_pos : 0 < (2 * I.len) := by nlinarith [I.len_pos]
  have hK_nonneg : 0 ≤ K_tail M := K_tail_nonneg M
  have h_cancel :
      Real.sqrt (K_tail M * (2 * I.len)) * (1 / Real.sqrt (2 * I.len)) = Real.sqrt (K_tail M) := by
    simpa using (sqrt_energy_cancellation (K_tail M) (2 * I.len) hK_nonneg h_len_pos)

  have h_rhs :
      C_geom * Real.sqrt (K_tail M * (2 * I.len)) * (1 / Real.sqrt (2 * I.len)) = U_tail M := by
    -- reassociate to expose the cancellation term
    rw [mul_assoc]
    -- cancel the length factor, then unfold `U_tail`
    simp [h_cancel, U_tail]

  have h_cofactor_phase' :
      ‖rgCofactorPhaseAngle ρ (I.t0 + I.len) - rgCofactorPhaseAngle ρ (I.t0 - I.len)‖ ≤
        U_tail M := by
    simpa [h_rhs] using h_cofactor_phase

  -- 5) Transport back across the algebraic reduction.
  simpa [h_reduce] using h_cofactor_phase'

end Port
end RiemannRecognitionGeometry
