import Mathlib.MeasureTheory.Integral.IntervalIntegral
import RiemannRecognitionGeometry.Port.XiCRGreenAssumptions
import RiemannRecognitionGeometry.Port.RealPhaseTransfer
import RiemannRecognitionGeometry.Phase

noncomputable section

namespace RiemannRecognitionGeometry
namespace Port

open Real MeasureTheory

namespace XiCRGreenS2Interfaces

/-!
# Port scaffold: minimal analytic interfaces for the xi-side CR/Green wall (S2-only)

This is the xi analogue of `Port/CofactorCRGreenS2Interfaces.lean`.

We want a faithful (analysis-friendly) route to the strong xi CR/Green bound:

`xiPhaseChange I ≤ C_geom * sqrt(xiEbox_poisson I) * |I|^{-1/2}`.

Instead of differentiating the principal-branch `argXi`, we introduce a real-valued phase lift
`θ_I : ℝ → ℝ` whose coercion agrees with `phaseXi` (mod `2π`) on the Whitney base, and require an
FTC-valid velocity density.
Then we combine:

1. **Green trace identity + FTC**: `Δθ_real = ∫ θ'`,
2. **Pairing bound**: `|∫ θ'| ≤ sqrt(Ebox) * (C_geom * |I|^{-1/2})`,
3. **Angle ≤ abs(real rep)**: `xiPhaseChange ≤ |Δθ_real|`.

No new analysis is proved here; this file only records the minimal interfaces and the wiring lemma
from those interfaces to `Port.XiCRGreenAssumptionsStrong`.
-/

/-- Subgate A (xi S2a): an FTC-valid trace identity for a real-valued phase lift of `phaseXi`
on Whitney bases. -/
structure GreenTraceIdentity where
  /-- A real-valued phase lift on the Whitney base. -/
  theta : WhitneyInterval → (ℝ → ℝ)

  /-- The lift agrees with the `Real.Angle` phase `phaseXi` on the Whitney base interval. -/
  coe_theta_eq :
    ∀ (I : WhitneyInterval) (t : ℝ),
      t ∈ I.interval → (theta I t : Real.Angle) = phaseXi t

  /-- A candidate phase-velocity density `dθ/dt` on the Whitney base. -/
  dPhase : WhitneyInterval → (ℝ → ℝ)

  /-- Pointwise derivative identification (FTC gate). -/
  hasDerivAt :
    ∀ (I : WhitneyInterval) (t : ℝ),
      t ∈ Set.uIcc (I.t0 - I.len) (I.t0 + I.len) →
        HasDerivAt (fun u => theta I u) (dPhase I t) t

  /-- Integrability of the phase-velocity density on the Whitney base. -/
  intervalIntegrable :
    ∀ I : WhitneyInterval,
      IntervalIntegrable (fun t => dPhase I t) volume (I.t0 - I.len) (I.t0 + I.len)

namespace GreenTraceIdentity

/-- The real phase change of the lift across the Whitney base. -/
def phaseChangeReal (T : GreenTraceIdentity) (I : WhitneyInterval) : ℝ :=
  T.theta I (I.t0 + I.len) - T.theta I (I.t0 - I.len)

/-- The lift phase change, coerced to `Real.Angle`, recovers `xiPhaseChangeAngle I`. -/
lemma coe_phaseChangeReal (T : GreenTraceIdentity) (I : WhitneyInterval) :
    (phaseChangeReal T I : Real.Angle) = xiPhaseChangeAngle I := by
  have ha : (I.t0 - I.len) ∈ I.interval := by
    refine ⟨?_, ?_⟩ <;> linarith [I.len_pos]
  have hb : (I.t0 + I.len) ∈ I.interval := by
    refine ⟨?_, ?_⟩ <;> linarith [I.len_pos]
  have hθa : (T.theta I (I.t0 - I.len) : Real.Angle) = phaseXi (I.t0 - I.len) :=
    T.coe_theta_eq I (I.t0 - I.len) ha
  have hθb : (T.theta I (I.t0 + I.len) : Real.Angle) = phaseXi (I.t0 + I.len) :=
    T.coe_theta_eq I (I.t0 + I.len) hb
  unfold phaseChangeReal
  -- `((x - y : ℝ) : Real.Angle) = (x : Real.Angle) - (y : Real.Angle)`.
  simpa [xiPhaseChangeAngle, Real.Angle.coe_sub, hθa, hθb]

/-- FTC: `Δθ_real = ∫ dPhase` on the Whitney base. -/
lemma phaseChange_eq_intervalIntegral (T : GreenTraceIdentity) (I : WhitneyInterval) :
    phaseChangeReal T I =
      ∫ t in (I.t0 - I.len)..(I.t0 + I.len), T.dPhase I t := by
  classical
  set a : ℝ := I.t0 - I.len
  set b : ℝ := I.t0 + I.len
  have hderiv :
      ∀ t ∈ Set.uIcc a b,
        HasDerivAt (fun u => T.theta I u) (T.dPhase I t) t := by
    intro t ht
    exact T.hasDerivAt I t (by simpa [a, b] using ht)
  have hint : IntervalIntegrable (fun t => T.dPhase I t) volume a b := by
    simpa [a, b] using T.intervalIntegrable I
  have hftc :
      (∫ t in a..b, T.dPhase I t) =
        T.theta I b - T.theta I a := by
    simpa using (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint)
  simpa [phaseChangeReal, a, b] using hftc.symm

end GreenTraceIdentity

/-- Subgate B (xi S2b): Cauchy–Schwarz / pairing bound for the boundary trace integrand. -/
structure PairingBound (T : GreenTraceIdentity) : Prop where
  bound :
    ∀ I : WhitneyInterval,
      |∫ t in (I.t0 - I.len)..(I.t0 + I.len), T.dPhase I t|
        ≤ Real.sqrt (xiEbox_poisson I) * (C_geom * (1 / Real.sqrt (2 * I.len)))

/-- Green trace identity + pairing bound ⇒ the **strong** xi CR/Green bound. -/
theorem xiCRGreenAssumptionsStrong_of_greenTrace_and_pairing
    (T : GreenTraceIdentity) (hB : PairingBound T) :
    XiCRGreenAssumptionsStrong := by
  refine ⟨?_⟩
  intro I
  have hFTC :
      GreenTraceIdentity.phaseChangeReal T I =
        ∫ t in (I.t0 - I.len)..(I.t0 + I.len), T.dPhase I t :=
    GreenTraceIdentity.phaseChange_eq_intervalIntegral T I
  have hAbs :
      |GreenTraceIdentity.phaseChangeReal T I| ≤
        Real.sqrt (xiEbox_poisson I) * (C_geom * (1 / Real.sqrt (2 * I.len))) := by
    simpa [hFTC] using (hB.bound I)
  have hnorm :
      xiPhaseChange I ≤ |GreenTraceIdentity.phaseChangeReal T I| := by
    -- `xiPhaseChange I = ‖xiPhaseChangeAngle I‖ = ‖((Δθ_real) : Real.Angle)‖ ≤ |Δθ_real|`.
    have h := realAngle_norm_coe_le_abs (GreenTraceIdentity.phaseChangeReal T I)
    have hcoe : (GreenTraceIdentity.phaseChangeReal T I : Real.Angle) = xiPhaseChangeAngle I :=
      GreenTraceIdentity.coe_phaseChangeReal T I
    -- rewrite the norm on the LHS to `xiPhaseChange`.
    simpa [xiPhaseChange, hcoe] using h
  have hAbs' :
      |GreenTraceIdentity.phaseChangeReal T I| ≤
        C_geom * Real.sqrt (xiEbox_poisson I) * (1 / Real.sqrt (2 * I.len)) := by
    -- commutativity/associativity only
    simpa [mul_assoc, mul_left_comm, mul_comm] using hAbs
  exact le_trans hnorm hAbs'

end XiCRGreenS2Interfaces

end Port
end RiemannRecognitionGeometry
