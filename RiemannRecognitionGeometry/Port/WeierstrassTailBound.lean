/-
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
    -- Avoid simp-normalizing `1 / √(2*I.len)` into an inverse-product; keep the exact form so `h_cancel` matches.
    unfold U_tail
    -- `U_tail M = C_geom * √(K_tail M)`, and `h_cancel` performs the √|I| cancellation.
    calc
      C_geom * Real.sqrt (K_tail M * (2 * I.len)) * (1 / Real.sqrt (2 * I.len))
          = C_geom * (Real.sqrt (K_tail M * (2 * I.len)) * (1 / Real.sqrt (2 * I.len))) := by
              rw [mul_assoc]
      _ = C_geom * Real.sqrt (K_tail M) := by
              rw [h_cancel]

  have h_cofactor_phase' :
      ‖rgCofactorPhaseAngle ρ (I.t0 + I.len) - rgCofactorPhaseAngle ρ (I.t0 - I.len)‖ ≤
        U_tail M := by
    -- Rewrite the goal using `h_rhs` (avoid `simp` rewriting the denominator).
    rw [← h_rhs]
    exact h_cofactor_phase

  -- 5) Transport back across the algebraic reduction.
  simpa [h_reduce] using h_cofactor_phase'

/-- Variant: derive the same tail bound from the **strong** energy-form CR/Green hypothesis.

This is the cleanest consumer-facing statement: it avoids the auxiliary “energy density”
parameter `E` in `HardyDirichletCRGreen` and works directly with `Ebox ρ I`. -/
theorem weierstrass_tail_bound_of_hardyDirichletStrong
    (Ebox : ℂ → WhitneyInterval → ℝ)
    (hCar : HardyDirichletCarlesonBudget Ebox)
    (hGreen : HardyDirichletCRGreenStrong Ebox)
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
  have hEbox_nonneg : 0 ≤ Ebox ρ I := hCar.Ebox_nonneg ρ I

  -- 3) Strong CR/Green converts energy into phase bound.
  have h_phase_strong :
      ‖rgCofactorPhaseAngle ρ (I.t0 + I.len) - rgCofactorPhaseAngle ρ (I.t0 - I.len)‖ ≤
        C_geom * Real.sqrt (Ebox ρ I) * (1 / Real.sqrt (2 * I.len)) :=
    hGreen.cofactor_phase_change_bound_strong I ρ

  -- 4) Replace `√(Ebox)` by `√(K_tail M * |I|)` and cancel `√|I|`.
  have h_len_pos : 0 < (2 * I.len) := by nlinarith [I.len_pos]
  have hK_nonneg : 0 ≤ K_tail M := K_tail_nonneg M
  have h_sqrt_le : Real.sqrt (Ebox ρ I) ≤ Real.sqrt (K_tail M * (2 * I.len)) :=
    Real.sqrt_le_sqrt h_energy
  have hden_nonneg : 0 ≤ (1 / Real.sqrt (2 * I.len) : ℝ) :=
    one_div_nonneg.mpr (Real.sqrt_nonneg _)
  have hC_nonneg : 0 ≤ (C_geom : ℝ) := by
    simp [RiemannRecognitionGeometry.C_geom]
  have h_rhs_le :
      C_geom * Real.sqrt (Ebox ρ I) * (1 / Real.sqrt (2 * I.len))
        ≤ C_geom * Real.sqrt (K_tail M * (2 * I.len)) * (1 / Real.sqrt (2 * I.len)) := by
    -- monotonicity in the middle factor
    have : C_geom * Real.sqrt (Ebox ρ I) ≤ C_geom * Real.sqrt (K_tail M * (2 * I.len)) :=
      mul_le_mul_of_nonneg_left h_sqrt_le hC_nonneg
    exact mul_le_mul_of_nonneg_right this hden_nonneg

  have h_cancel :
      Real.sqrt (K_tail M * (2 * I.len)) * (1 / Real.sqrt (2 * I.len)) = Real.sqrt (K_tail M) := by
    simpa using (sqrt_energy_cancellation (K_tail M) (2 * I.len) hK_nonneg h_len_pos)

  have h_final :
      ‖rgCofactorPhaseAngle ρ (I.t0 + I.len) - rgCofactorPhaseAngle ρ (I.t0 - I.len)‖ ≤ U_tail M := by
    -- chain the inequalities
    have h1 : ‖rgCofactorPhaseAngle ρ (I.t0 + I.len) - rgCofactorPhaseAngle ρ (I.t0 - I.len)‖ ≤
        C_geom * Real.sqrt (K_tail M * (2 * I.len)) * (1 / Real.sqrt (2 * I.len)) :=
      le_trans h_phase_strong h_rhs_le
    -- cancel √|I| and rewrite to `U_tail`
    have hEq :
        C_geom * Real.sqrt (K_tail M * (2 * I.len)) * (1 / Real.sqrt (2 * I.len)) = U_tail M := by
      unfold U_tail
      -- keep the same associativity so `h_cancel` matches
      calc
        C_geom * Real.sqrt (K_tail M * (2 * I.len)) * (1 / Real.sqrt (2 * I.len))
            = C_geom * (Real.sqrt (K_tail M * (2 * I.len)) * (1 / Real.sqrt (2 * I.len))) := by
                rw [mul_assoc]
        _ = C_geom * Real.sqrt (K_tail M) := by
                rw [h_cancel]
    exact le_trans h1 (le_of_eq hEq)

  -- 5) Transport back across the algebraic reduction.
  simpa [h_reduce] using h_final

end Port
end RiemannRecognitionGeometry
