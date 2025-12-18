/-!
# Port step: a non-vacuous tail bound route using `cofactorEbox_poisson`

At this point we have:

- a concrete energy functional `Ebox := cofactorEbox_poisson` (`Port/CofactorEnergy.lean`), and
- a Carleson budget instance for it:
  `hardyDirichletCarlesonBudget_cofactorEbox_poisson`
  (`Port/CofactorCarlesonBudget.lean`), derived from the existing Fefferman–Stein axiom.

The remaining missing analytic input is the **CR/Green** inequality converting that energy bound into
a bound on the cofactor phase change (`HardyDirichletCRGreen`).

This repo already carries a (classical-analysis) assumption field
`ClassicalAnalysisAssumptions.cofactor_green_identity_axiom_statement`.
While it is not yet phrased in terms of an explicit energy functional, it implies the
`HardyDirichletCRGreen` interface immediately (as a placeholder).

This file packages that implication and derives the RG-style tail bound as a theorem that depends on:

- the BMO certificate `InBMOWithBound (cofactorLogAbs ρ) M`,
- the existing Fefferman–Stein axiom, and
- the existing cofactor Green/CR assumption.

This is a useful intermediate waypoint: it isolates the next real work item as proving the CR/Green
bound *faithfully* (energy → phase) and proving BMO inheritance for the cofactor boundary data.
-/

import RiemannRecognitionGeometry.Assumptions
import RiemannRecognitionGeometry.Port.CofactorCarlesonBudget
import RiemannRecognitionGeometry.Port.CofactorCRGreenAssumptions
import RiemannRecognitionGeometry.Port.WeierstrassTailBound

noncomputable section

namespace RiemannRecognitionGeometry
namespace Port

open Real Complex

/-- Placeholder: the current project-level cofactor Green/CR assumption implies the
Hardy/Dirichlet CRGreen interface for any `Ebox` (it does not actually depend on `Ebox` yet). -/
theorem hardyDirichletCRGreen_of_ClassicalAnalysisAssumptions
    (hCA : ClassicalAnalysisAssumptions) :
    HardyDirichletCRGreen cofactorEbox_poisson := by
  -- Route through the energy-based target bundle (still non-faithful until a true Green pairing proof lands).
  exact
    hardyDirichletCRGreen_of_cofactorCRGreenAssumptions
      (cofactorCRGreenAssumptions_of_ClassicalAnalysisAssumptions hCA)

/-- Tail bound for `Ebox := cofactorEbox_poisson`, assuming an explicit Hardy/Dirichlet CRGreen interface. -/
theorem weierstrass_tail_bound_cofactorEbox_poisson_of_hardyDirichletCRGreen
    (hGreen : HardyDirichletCRGreen cofactorEbox_poisson)
    (I : WhitneyInterval) (ρ : ℂ) (M : ℝ)
    (h_bmo : InBMOWithBound (cofactorLogAbs ρ) M)
    (hρ_zero : completedRiemannZeta ρ = 0) (hρ_im : ρ.im ∈ I.interval) :
    let d : ℝ := ρ.re - 1/2
    let y_hi : ℝ := I.t0 + I.len - ρ.im
    let y_lo : ℝ := I.t0 - I.len - ρ.im
    let blaschke := Real.arctan (y_lo / d) - Real.arctan (y_hi / d)
    ‖xiPhaseChangeAngle I - (blaschke : Real.Angle)‖ ≤ U_tail M := by
  -- Assemble the Hardy/Dirichlet interfaces for `Ebox := cofactorEbox_poisson`.
  let hCar : HardyDirichletCarlesonBudget cofactorEbox_poisson :=
    hardyDirichletCarlesonBudget_cofactorEbox_poisson
  -- Apply the generic derivation lemma.
  have hM_pos : 0 < M := h_bmo.1
  simpa using
    (weierstrass_tail_bound_of_hardyDirichlet
      (Ebox := cofactorEbox_poisson)
      (hCar := hCar) (hGreen := hGreen)
      (I := I) (ρ := ρ) (M := M) (hM_pos := hM_pos)
      (h_bmo := h_bmo) (hρ_zero := hρ_zero) (hρ_im := hρ_im))

/-- Tail bound for `Ebox := cofactorEbox_poisson`, assuming the energy-based cofactor CR/Green target bundle. -/
theorem weierstrass_tail_bound_cofactorEbox_poisson_of_cofactorCRGreenAssumptions
    (h : CofactorCRGreenAssumptions)
    (I : WhitneyInterval) (ρ : ℂ) (M : ℝ)
    (h_bmo : InBMOWithBound (cofactorLogAbs ρ) M)
    (hρ_zero : completedRiemannZeta ρ = 0) (hρ_im : ρ.im ∈ I.interval) :
    let d : ℝ := ρ.re - 1/2
    let y_hi : ℝ := I.t0 + I.len - ρ.im
    let y_lo : ℝ := I.t0 - I.len - ρ.im
    let blaschke := Real.arctan (y_lo / d) - Real.arctan (y_hi / d)
    ‖xiPhaseChangeAngle I - (blaschke : Real.Angle)‖ ≤ U_tail M := by
  exact
    weierstrass_tail_bound_cofactorEbox_poisson_of_hardyDirichletCRGreen
      (hGreen := hardyDirichletCRGreen_of_cofactorCRGreenAssumptions h)
      (I := I) (ρ := ρ) (M := M)
      (h_bmo := h_bmo) (hρ_zero := hρ_zero) (hρ_im := hρ_im)

/-- Tail bound for the concrete energy functional `cofactorEbox_poisson`, assuming:

- a BMO certificate for the cofactor boundary log-modulus, and
- the (currently axiomatized) cofactor Green/CR inequality from `ClassicalAnalysisAssumptions`.
-/
theorem weierstrass_tail_bound_cofactorEbox_poisson
    (hCA : ClassicalAnalysisAssumptions)
    (I : WhitneyInterval) (ρ : ℂ) (M : ℝ)
    (h_bmo : InBMOWithBound (cofactorLogAbs ρ) M)
    (hρ_zero : completedRiemannZeta ρ = 0) (hρ_im : ρ.im ∈ I.interval) :
    let d : ℝ := ρ.re - 1/2
    let y_hi : ℝ := I.t0 + I.len - ρ.im
    let y_lo : ℝ := I.t0 - I.len - ρ.im
    let blaschke := Real.arctan (y_lo / d) - Real.arctan (y_hi / d)
    ‖xiPhaseChangeAngle I - (blaschke : Real.Angle)‖ ≤ U_tail M := by
  -- Route through the generic lemma, using the project-level cofactor Green assumption to get `CRGreen`.
  exact
    weierstrass_tail_bound_cofactorEbox_poisson_of_hardyDirichletCRGreen
      (hGreen := hardyDirichletCRGreen_of_ClassicalAnalysisAssumptions (hCA := hCA))
      (I := I) (ρ := ρ) (M := M)
      (h_bmo := h_bmo) (hρ_zero := hρ_zero) (hρ_im := hρ_im)

end Port
end RiemannRecognitionGeometry
