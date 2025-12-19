import RiemannRecognitionGeometry.Port.XiEnergy
import RiemannRecognitionGeometry.Port.XiCRGreenAssumptions
import RiemannRecognitionGeometry.Port.RealPhaseTransfer

noncomputable section

namespace RiemannRecognitionGeometry
namespace Port

open Real

/-!
# Port scaffold: minimal subgates for the **strong** xi CR/Green bound

This is the xi analogue of `Port/CofactorCRGreenSubgates.lean`.

The strong energy-form xi CR/Green estimate is:

`xiPhaseChange I ≤ C_geom * sqrt(xiEbox_poisson I) * |I|^{-1/2}`.

We decompose this into three independent subgates:

1. **Phase representative**: a real-valued representative `Δθ_real` whose absolute value controls
   `xiPhaseChange` (a `Real.Angle` norm).
2. **Green+Cauchy–Schwarz pairing**: `|Δθ_real| ≤ sqrt(Ebox) * sqrt(E_window)`.
3. **Window energy bound**: `sqrt(E_window) ≤ C_geom * |I|^{-1/2}`.

Once (2) and (3) are available, (1) upgrades to the desired strong bound, yielding
`Port.XiCRGreenAssumptionsStrong`.

No analysis is proved here: this file is an interface decomposition / wiring layer.
-/

/-- Minimal analytic subgates sufficient for the **strong** xi CR/Green bound,
specialized to the concrete energy functional `Ebox := xiEbox_poisson`. -/
structure XiCRGreenSubgatesStrong where
  /-- A real-valued phase-change representative for the xi phase. -/
  phaseChangeReal : WhitneyInterval → ℝ

  /-- The `Real.Angle` norm is controlled by the absolute value of the real representative. -/
  angle_le_abs_real :
    ∀ I : WhitneyInterval, xiPhaseChange I ≤ |phaseChangeReal I|

  /-- Abstract “window energy” term (depends only on the interval `I`). -/
  windowEnergy : WhitneyInterval → ℝ

  /-- Cauchy–Schwarz pairing: the real phase change is bounded by the product of square-roots
  of the xi box energy and the window energy. -/
  green_pairing_cauchy_schwarz :
    ∀ I : WhitneyInterval,
      |phaseChangeReal I| ≤
        Real.sqrt (xiEbox_poisson I) * Real.sqrt (windowEnergy I)

  /-- Window-energy bound with the right scaling. This is the part that produces the
  `|I|^{-1/2}` factor. -/
  windowEnergy_sqrt_bound :
    ∀ I : WhitneyInterval,
      Real.sqrt (windowEnergy I) ≤ C_geom * (1 / Real.sqrt (2 * I.len))

namespace XiCRGreenSubgatesStrong

/-!
## Default real representative (S1 is already solved in this repo)

For xi we can take the real representative to be `actualPhaseSignal I`, and the subgate (S1)
is exactly `Port.xiPhaseChange_le_abs_actualPhaseSignal` from `Port/RealPhaseTransfer.lean`.
-/

/-- Default real-valued phase-change representative for the xi phase. -/
def phaseChangeReal_default (I : WhitneyInterval) : ℝ :=
  actualPhaseSignal I

/-- Subgate (S1): `xiPhaseChange I` is controlled by the absolute value of the default real representative. -/
lemma angle_le_abs_real_default (I : WhitneyInterval) :
    xiPhaseChange I ≤ |phaseChangeReal_default I| := by
  simpa [phaseChangeReal_default] using xiPhaseChange_le_abs_actualPhaseSignal I

/-- A default choice of window energy with the correct `|I|^{-1/2}` scaling built in. -/
def windowEnergy_default (I : WhitneyInterval) : ℝ :=
  (C_geom * (1 / Real.sqrt (2 * I.len))) ^ 2

/-- Subgate (S3): the window-energy scaling bound holds for `windowEnergy_default`. -/
lemma windowEnergy_sqrt_bound_default (I : WhitneyInterval) :
    Real.sqrt (windowEnergy_default I) ≤ C_geom * (1 / Real.sqrt (2 * I.len)) := by
  have hC : 0 ≤ (C_geom : ℝ) := by
    simp [RiemannRecognitionGeometry.C_geom]
  have hden : 0 ≤ (1 / Real.sqrt (2 * I.len) : ℝ) :=
    one_div_nonneg.mpr (Real.sqrt_nonneg _)
  have hx : 0 ≤ (C_geom * (1 / Real.sqrt (2 * I.len)) : ℝ) := mul_nonneg hC hden
  have habs :
      |(C_geom * (1 / Real.sqrt (2 * I.len)) : ℝ)| = C_geom * (1 / Real.sqrt (2 * I.len)) :=
    abs_of_nonneg hx
  have : Real.sqrt (windowEnergy_default I) = |(C_geom * (1 / Real.sqrt (2 * I.len)) : ℝ)| := by
    simp [windowEnergy_default, Real.sqrt_sq_eq_abs]
  calc
    Real.sqrt (windowEnergy_default I)
        = |(C_geom * (1 / Real.sqrt (2 * I.len)) : ℝ)| := this
    _ = C_geom * (1 / Real.sqrt (2 * I.len)) := habs
    _ ≤ C_geom * (1 / Real.sqrt (2 * I.len)) := le_rfl

/-- Build the subgate bundle by fixing (S1) to the default real representative. -/
def of_realPhaseTransfer
    (windowEnergy : WhitneyInterval → ℝ)
    (hGreen :
      ∀ I : WhitneyInterval,
        |phaseChangeReal_default I| ≤
          Real.sqrt (xiEbox_poisson I) * Real.sqrt (windowEnergy I))
    (hWin :
      ∀ I : WhitneyInterval,
        Real.sqrt (windowEnergy I) ≤ C_geom * (1 / Real.sqrt (2 * I.len))) :
    XiCRGreenSubgatesStrong where
  phaseChangeReal := phaseChangeReal_default
  angle_le_abs_real := by
    intro I
    simpa using angle_le_abs_real_default I
  windowEnergy := windowEnergy
  green_pairing_cauchy_schwarz := by
    intro I
    simpa using hGreen I
  windowEnergy_sqrt_bound := hWin

/-- Convenience: build the subgate bundle using the default real representative (S1) and the
default window-energy scaling (S3). The remaining analytic input is exactly the Green/C–S pairing
inequality (S2). -/
def of_realPhaseTransfer_defaultWindow
    (hGreen :
      ∀ I : WhitneyInterval,
        |phaseChangeReal_default I| ≤
          Real.sqrt (xiEbox_poisson I) * Real.sqrt (windowEnergy_default I)) :
    XiCRGreenSubgatesStrong :=
  of_realPhaseTransfer
    (windowEnergy := windowEnergy_default)
    (hGreen := hGreen)
    (hWin := windowEnergy_sqrt_bound_default)

end XiCRGreenSubgatesStrong

/-- The subgates imply the strong xi CR/Green assumption used by the RG/Port pipeline. -/
theorem xiCRGreenAssumptionsStrong_of_subgates
    (h : XiCRGreenSubgatesStrong) :
    XiCRGreenAssumptionsStrong := by
  refine ⟨?_⟩
  intro I
  -- 1) angle norm ≤ abs(real rep)
  have h_angle : xiPhaseChange I ≤ |h.phaseChangeReal I| :=
    h.angle_le_abs_real I
  -- 2) abs(real rep) ≤ √Ebox * √Ewindow
  have h_cs :
      |h.phaseChangeReal I| ≤
        Real.sqrt (xiEbox_poisson I) * Real.sqrt (h.windowEnergy I) :=
    h.green_pairing_cauchy_schwarz I
  -- 3) √Ewindow ≤ C_geom * |I|^{-1/2}
  have h_win : Real.sqrt (h.windowEnergy I) ≤ C_geom * (1 / Real.sqrt (2 * I.len)) :=
    h.windowEnergy_sqrt_bound I
  -- Combine (2) and (3).
  have h_abs :
      |h.phaseChangeReal I| ≤
        C_geom * Real.sqrt (xiEbox_poisson I) * (1 / Real.sqrt (2 * I.len)) := by
    have h0 :
        Real.sqrt (xiEbox_poisson I) * Real.sqrt (h.windowEnergy I)
          ≤ Real.sqrt (xiEbox_poisson I) * (C_geom * (1 / Real.sqrt (2 * I.len))) :=
      mul_le_mul_of_nonneg_left h_win (Real.sqrt_nonneg _)
    have h1 :
        Real.sqrt (xiEbox_poisson I) * (C_geom * (1 / Real.sqrt (2 * I.len)))
          = C_geom * Real.sqrt (xiEbox_poisson I) * (1 / Real.sqrt (2 * I.len)) := by
      ac_rfl
    exact le_trans (le_trans h_cs h0) (le_of_eq h1)
  -- Final.
  exact le_trans h_angle h_abs

end Port
end RiemannRecognitionGeometry
