/-
# Port step: transfer bounds from real-valued phases to `Real.Angle`

The `reality` CR/Green blueprint is naturally phrased in terms of real-valued phase functions and
their boundary pairings/integrals.

In this repo, Recognition Geometry models phase **modulo 2π** using `Real.Angle`, and the RG spine
uses `xiPhaseChange` / `rgCofactorPhaseAngle` (norm in `Real.Angle`).

This file provides small, purely algebraic “transfer” lemmas:

- any bound on an ℝ-valued phase difference yields a bound on the corresponding `Real.Angle` norm,
  since the `Real.Angle` norm is the minimal representative and hence ≤ `abs` of any chosen representative.

We also package “real-valued CR/Green” targets that imply the existing energy-based Port targets.
-/

import RiemannRecognitionGeometry.Port.XiEnergy
import RiemannRecognitionGeometry.Port.XiCRGreenAssumptions
import RiemannRecognitionGeometry.Port.CofactorCRGreenAssumptions
import RiemannRecognitionGeometry.Phase

noncomputable section

namespace RiemannRecognitionGeometry
namespace Port

open Real Complex

/-! ## Basic lemma: `‖(x : Real.Angle)‖ ≤ |x|` -/

lemma realAngle_norm_coe_le_abs (x : ℝ) : ‖(x : Real.Angle)‖ ≤ |x| := by
  -- Work with `p = 2π`.
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by nlinarith [Real.pi_pos]
  have hpos : 0 < (2 * Real.pi : ℝ) := by nlinarith [Real.pi_pos]
  have h_half : |(2 * Real.pi : ℝ)| / 2 = Real.pi := by
    calc
      |(2 * Real.pi : ℝ)| / 2 = (2 * Real.pi) / 2 := by simp [abs_of_pos hpos]
      _ = Real.pi := by
            simpa [mul_comm] using
              (mul_div_cancel_left₀ (Real.pi) (2 : ℝ) (two_ne_zero : (2 : ℝ) ≠ 0))
  by_cases hx : |x| ≤ Real.pi
  · -- Small representative: norm equals abs.
    have hx' : |x| ≤ |(2 * Real.pi : ℝ)| / 2 := by simpa [h_half] using hx
    have h_eq :
        ‖(x : Real.Angle)‖ = |x| := (AddCircle.norm_coe_eq_abs_iff (p := (2 * Real.pi)) (x := x) hp).2 hx'
    simpa [h_eq]
  · -- Large representative: norm ≤ π < |x|.
    have hx' : Real.pi < |x| := lt_of_not_ge hx
    have hnorm : ‖(x : Real.Angle)‖ ≤ Real.pi := by
      have h := AddCircle.norm_le_half_period (p := (2 * Real.pi)) (x := (x : Real.Angle)) hp
      simpa [h_half] using h
    exact le_trans hnorm (le_of_lt hx')

/-! ## Transfer for `xiPhaseChange` via `actualPhaseSignal` -/

lemma xiPhaseChangeAngle_eq_coe_actualPhaseSignal (I : WhitneyInterval) :
    xiPhaseChangeAngle I = (actualPhaseSignal I : Real.Angle) := by
  -- `phaseXi t` is `argXi t` coerced into `Real.Angle`.
  simp [xiPhaseChangeAngle, phaseXi, actualPhaseSignal, argXi, Real.Angle.coe_sub]

lemma xiPhaseChange_le_abs_actualPhaseSignal (I : WhitneyInterval) :
    xiPhaseChange I ≤ |actualPhaseSignal I| := by
  unfold xiPhaseChange
  -- rewrite the angle difference as a coercion of the real difference
  have h := realAngle_norm_coe_le_abs (actualPhaseSignal I)
  simpa [xiPhaseChangeAngle_eq_coe_actualPhaseSignal] using h

/-! ## Real-valued cofactor phase corresponding to `rgCofactorPhaseAngle` -/

/-- A real-valued phase representative whose coercion to `Real.Angle` equals `rgCofactorPhaseAngle`. -/
def rgCofactorPhaseReal (ρ : ℂ) (t : ℝ) : ℝ :=
  argXi t + rgBlaschkePhase ρ t

lemma rgCofactorPhaseAngle_eq_coe (ρ : ℂ) (t : ℝ) :
    rgCofactorPhaseAngle ρ t = (rgCofactorPhaseReal ρ t : Real.Angle) := by
  simp [rgCofactorPhaseAngle, rgCofactorPhaseReal, phaseXi, argXi, Real.Angle.coe_add]

lemma cofactorPhaseChange_le_abs_real (I : WhitneyInterval) (ρ : ℂ) :
    ‖rgCofactorPhaseAngle ρ (I.t0 + I.len) - rgCofactorPhaseAngle ρ (I.t0 - I.len)‖ ≤
      |rgCofactorPhaseReal ρ (I.t0 + I.len) - rgCofactorPhaseReal ρ (I.t0 - I.len)| := by
  -- Rewrite the `Real.Angle` difference as a coercion of the real difference.
  have h :
      rgCofactorPhaseAngle ρ (I.t0 + I.len) - rgCofactorPhaseAngle ρ (I.t0 - I.len) =
        ((rgCofactorPhaseReal ρ (I.t0 + I.len) - rgCofactorPhaseReal ρ (I.t0 - I.len)) : ℝ) := by
    -- The RHS is coerced to `Real.Angle`; `simp` uses `Real.Angle.coe_sub`.
    simp [rgCofactorPhaseAngle_eq_coe, Real.Angle.coe_sub]
  -- Apply `‖(x : Real.Angle)‖ ≤ |x|`.
  have h0 := realAngle_norm_coe_le_abs (rgCofactorPhaseReal ρ (I.t0 + I.len) - rgCofactorPhaseReal ρ (I.t0 - I.len))
  simpa [h] using h0

/-! ## “Real-valued CR/Green” targets implying the existing energy-based targets -/

structure XiCRGreenAssumptionsReal : Prop where
  /-- Energy→phase bound for the real-valued phase difference `actualPhaseSignal`. -/
  argXi_green_from_energy :
    ∀ (I : WhitneyInterval) (E : ℝ),
      0 < E →
      xiEbox_poisson I ≤ E * (2 * I.len) →
      |actualPhaseSignal I| ≤
        C_geom * Real.sqrt (E * (2 * I.len)) * (1 / Real.sqrt (2 * I.len))

theorem xiCRGreenAssumptions_of_real (h : XiCRGreenAssumptionsReal) : XiCRGreenAssumptions := by
  refine ⟨?_⟩
  intro I E hE_pos hEbox
  have h1 : xiPhaseChange I ≤ |actualPhaseSignal I| :=
    xiPhaseChange_le_abs_actualPhaseSignal I
  have h2 : |actualPhaseSignal I| ≤ C_geom * Real.sqrt (E * (2 * I.len)) * (1 / Real.sqrt (2 * I.len)) :=
    h.argXi_green_from_energy I E hE_pos hEbox
  exact le_trans h1 h2

structure CofactorCRGreenAssumptionsReal : Prop where
  /-- Energy→phase bound for the real-valued representative `rgCofactorPhaseReal`. -/
  cofactor_green_from_energy_real :
    ∀ (I : WhitneyInterval) (ρ : ℂ) (E : ℝ),
      0 < E →
      cofactorEbox_poisson ρ I ≤ E * (2 * I.len) →
      |rgCofactorPhaseReal ρ (I.t0 + I.len) - rgCofactorPhaseReal ρ (I.t0 - I.len)| ≤
        C_geom * Real.sqrt (E * (2 * I.len)) * (1 / Real.sqrt (2 * I.len))

theorem cofactorCRGreenAssumptions_of_real (h : CofactorCRGreenAssumptionsReal) :
    CofactorCRGreenAssumptions := by
  refine ⟨?_⟩
  intro I ρ E hE_pos hEbox
  have h1 :
      ‖rgCofactorPhaseAngle ρ (I.t0 + I.len) - rgCofactorPhaseAngle ρ (I.t0 - I.len)‖ ≤
        |rgCofactorPhaseReal ρ (I.t0 + I.len) - rgCofactorPhaseReal ρ (I.t0 - I.len)| :=
    cofactorPhaseChange_le_abs_real I ρ
  have h2 :
      |rgCofactorPhaseReal ρ (I.t0 + I.len) - rgCofactorPhaseReal ρ (I.t0 - I.len)| ≤
        C_geom * Real.sqrt (E * (2 * I.len)) * (1 / Real.sqrt (2 * I.len)) :=
    h.cofactor_green_from_energy_real I ρ E hE_pos hEbox
  exact le_trans h1 h2

end Port
end RiemannRecognitionGeometry
