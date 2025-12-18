import RiemannRecognitionGeometry.Port.CofactorEnergy
import RiemannRecognitionGeometry.Port.CofactorCRGreenAssumptions
import RiemannRecognitionGeometry.Port.RealPhaseTransfer

noncomputable section

namespace RiemannRecognitionGeometry
namespace Port

open Real Complex

/-!
# Port scaffold: minimal subgates for the **strong** cofactor CR/Green bound

The current boxed RG hard wall is the strong energy-form CR/Green estimate:

`‖Δθ_cofactor‖ ≤ C_geom * sqrt(Ebox) * |I|^{-1/2}`.

This file records a *minimal* (and faithful) decomposition of that statement into three
independent analytic subgates, matching the structure of the `riemann-finish` CR/Green chain:

1. **Phase representative**: a real-valued representative `Δθ_real` whose absolute value controls
   the `Real.Angle` phase norm.
2. **Green+Cauchy–Schwarz pairing**: `|Δθ_real| ≤ sqrt(Ebox) * sqrt(E_window)`.
3. **Window energy bound**: `sqrt(E_window) ≤ C_geom * |I|^{-1/2}`.

Once (2) and (3) are available, (1) upgrades to the desired `Real.Angle` norm bound, giving
`Port.CofactorCRGreenAssumptionsStrong`.

This turns the monolithic “prove CR/Green” wall into: prove (2) + (3) + (boundary-term gate)
inside whatever analytic model you prefer.
-/

/-- Minimal analytic subgates sufficient for the **strong** cofactor CR/Green bound,
specialized to the concrete energy functional `Ebox := cofactorEbox_poisson`.

This is a data-bearing bundle (not a `Prop` structure), since it contains auxiliary objects
like a real-valued phase representative and a window-energy functional. -/
structure CofactorCRGreenSubgatesStrong where
  /-- A real-valued phase-change representative for the cofactor phase. -/
  phaseChangeReal : WhitneyInterval → ℂ → ℝ

  /-- The `Real.Angle` norm is controlled by the absolute value of the real representative. -/
  angle_le_abs_real :
    ∀ (I : WhitneyInterval) (ρ : ℂ),
      ‖rgCofactorPhaseAngle ρ (I.t0 + I.len) - rgCofactorPhaseAngle ρ (I.t0 - I.len)‖ ≤
        |phaseChangeReal I ρ|

  /-- Abstract “window energy” term (depends only on the interval `I`). -/
  windowEnergy : WhitneyInterval → ℝ

  /-- Cauchy–Schwarz pairing: the real phase change is bounded by the product of square-roots
  of the cofactor box energy and the window energy. -/
  green_pairing_cauchy_schwarz :
    ∀ (I : WhitneyInterval) (ρ : ℂ),
      |phaseChangeReal I ρ| ≤
        Real.sqrt (cofactorEbox_poisson ρ I) * Real.sqrt (windowEnergy I)

  /-- Window-energy bound with the right scaling. This is the part that produces the
  `|I|^{-1/2}` factor. -/
  windowEnergy_sqrt_bound :
    ∀ I : WhitneyInterval,
      Real.sqrt (windowEnergy I) ≤ C_geom * (1 / Real.sqrt (2 * I.len))

/-
## Default real representative (S1 is already solved in this repo)

We can take the real representative of the cofactor phase change to be the difference of
`rgCofactorPhaseReal` (see `Port/RealPhaseTransfer.lean`). The `Real.Angle` norm bound
`‖Δθ_angle‖ ≤ |Δθ_real|` is already proved there as
`Port.cofactorPhaseChange_le_abs_real`.
-/

namespace CofactorCRGreenSubgatesStrong

/-- Default real-valued phase-change representative for the cofactor phase. -/
def phaseChangeReal_default (I : WhitneyInterval) (ρ : ℂ) : ℝ :=
  rgCofactorPhaseReal ρ (I.t0 + I.len) - rgCofactorPhaseReal ρ (I.t0 - I.len)

/-- Subgate (S1): the `Real.Angle` norm of the cofactor phase change is controlled by the absolute
value of the default real representative. -/
lemma angle_le_abs_real_default (I : WhitneyInterval) (ρ : ℂ) :
    ‖rgCofactorPhaseAngle ρ (I.t0 + I.len) - rgCofactorPhaseAngle ρ (I.t0 - I.len)‖ ≤
      |phaseChangeReal_default I ρ| := by
  simpa [phaseChangeReal_default] using (cofactorPhaseChange_le_abs_real I ρ)

/-- Build the subgate bundle by fixing (S1) to the default real representative. -/
def of_realPhaseTransfer
    (windowEnergy : WhitneyInterval → ℝ)
    (hGreen :
      ∀ (I : WhitneyInterval) (ρ : ℂ),
        |phaseChangeReal_default I ρ| ≤
          Real.sqrt (cofactorEbox_poisson ρ I) * Real.sqrt (windowEnergy I))
    (hWin :
      ∀ I : WhitneyInterval,
        Real.sqrt (windowEnergy I) ≤ C_geom * (1 / Real.sqrt (2 * I.len))) :
    CofactorCRGreenSubgatesStrong where
  phaseChangeReal := phaseChangeReal_default
  angle_le_abs_real := by
    intro I ρ
    simpa using angle_le_abs_real_default I ρ
  windowEnergy := windowEnergy
  green_pairing_cauchy_schwarz := by
    intro I ρ
    simpa using hGreen I ρ
  windowEnergy_sqrt_bound := hWin

end CofactorCRGreenSubgatesStrong

/-- The subgates imply the strong cofactor CR/Green assumption used by the RG pipeline. -/
theorem cofactorCRGreenAssumptionsStrong_of_subgates
    (h : CofactorCRGreenSubgatesStrong) :
    CofactorCRGreenAssumptionsStrong := by
  refine ⟨?_⟩
  intro I ρ
  -- 1) angle norm ≤ abs(real rep)
  have h_angle : ‖rgCofactorPhaseAngle ρ (I.t0 + I.len) - rgCofactorPhaseAngle ρ (I.t0 - I.len)‖ ≤
      |h.phaseChangeReal I ρ| :=
    h.angle_le_abs_real I ρ
  -- 2) abs(real rep) ≤ √Ebox * √Ewindow
  have h_cs :
      |h.phaseChangeReal I ρ| ≤
        Real.sqrt (cofactorEbox_poisson ρ I) * Real.sqrt (h.windowEnergy I) :=
    h.green_pairing_cauchy_schwarz I ρ
  -- 3) √Ewindow ≤ C_geom * |I|^{-1/2}
  have h_win : Real.sqrt (h.windowEnergy I) ≤ C_geom * (1 / Real.sqrt (2 * I.len)) :=
    h.windowEnergy_sqrt_bound I
  -- Combine (2) and (3) to bound abs(real rep) by the desired RHS.
  have h_abs :
      |h.phaseChangeReal I ρ| ≤
        C_geom * Real.sqrt (cofactorEbox_poisson ρ I) * (1 / Real.sqrt (2 * I.len)) := by
    have h0 :
        Real.sqrt (cofactorEbox_poisson ρ I) * Real.sqrt (h.windowEnergy I)
          ≤ Real.sqrt (cofactorEbox_poisson ρ I) * (C_geom * (1 / Real.sqrt (2 * I.len))) :=
      mul_le_mul_of_nonneg_left h_win (Real.sqrt_nonneg _)
    have h1 :
        Real.sqrt (cofactorEbox_poisson ρ I) * (C_geom * (1 / Real.sqrt (2 * I.len)))
          = C_geom * Real.sqrt (cofactorEbox_poisson ρ I) * (1 / Real.sqrt (2 * I.len)) := by
      -- Pure associativity/commutativity; avoid rewriting `1 / √(2*len)` into inverse products.
      ac_rfl
    exact le_trans (le_trans h_cs h0) (le_of_eq h1)
  -- Final: angle ≤ RHS.
  exact le_trans h_angle h_abs

end Port
end RiemannRecognitionGeometry
