/-
# Port step: RG main theorems without `RGAssumptions` (using Port inheritance)

This file provides “drop-in alternative” versions of the RG main theorems in
`RiemannRecognitionGeometry/Main.lean` that remove the `RGAssumptions` parameter.

They replace the `zero_free_with_interval` contradiction step by the Port version
`Port.zero_free_with_interval_of_inheritance`, which depends on:

- `ClassicalAnalysisAssumptions` (for the phase upper bound), and
- `Port.CofactorBMOInheritance` (to produce the cofactor BMO certificate from `logAbsXi`).

**Update**: with the current Port model `cofactorLogAbs ρ = logAbsXi`, the inheritance bridge is
definitionally trivial (`cofactorBMOInheritance_trivial`), so we also provide convenience wrappers
that do *not* take `hInh` as an argument.

This matches the Reality port plan direction: eliminate the RG-specific “energy existence” axiom bundle and instead
expose the true missing analytic interfaces.
-/

import RiemannRecognitionGeometry.Main
import RiemannRecognitionGeometry.Port.ZeroFreeWithInterval
import RiemannRecognitionGeometry.Port.CofactorBMOInheritance
import RiemannRecognitionGeometry.Port.CofactorCRGreenAssumptions
import RiemannRecognitionGeometry.Port.XiCRGreenAssumptions
import RiemannRecognitionGeometry.Port.EnergyCRGreenAssumptions
import RiemannRecognitionGeometry.Port.RealPhaseTransfer
import RiemannRecognitionGeometry.Port.EnergyCRGreenAssumptionsReal

noncomputable section

namespace RiemannRecognitionGeometry
namespace Port

open Complex Set

/-- Port analogue of `Main.no_off_critical_zeros_in_strip`, removing `RGAssumptions`. -/
theorem no_off_critical_zeros_in_strip
    (hCA : ClassicalAnalysisAssumptions)
    (hInh : CofactorBMOInheritance)
    (M : ℝ) (h_osc : InBMOWithBound logAbsXi M) (hM_le : M ≤ C_tail) :
    ∀ ρ : ℂ, completedRiemannZeta ρ = 0 → ρ ∈ criticalStrip → False := by
  intro ρ hρ_zero hρ_crit
  simp only [criticalStrip, Set.mem_setOf_eq] at hρ_crit
  by_cases h_re_gt_one : 1 < ρ.re
  · -- Re(ρ) > 1: contradiction since ξ has no zeros there (Euler product)
    exact completedRiemannZeta_ne_zero_of_re_gt_one h_re_gt_one hρ_zero
  · -- 1/2 < Re(ρ) ≤ 1: use the Port centered contradiction
    push_neg at h_re_gt_one
    have hρ_re : 1/2 < ρ.re := hρ_crit
    exact
      Port.zero_free_with_interval_of_inheritance
        (ρ := ρ) (hCA := hCA) (hInh := hInh)
        (hρ_re := hρ_re) (hρ_zero := hρ_zero)
        (M := M) (h_osc := h_osc) (hM_le := hM_le)

/-- Port analogue of `Main.no_off_critical_zeros_in_strip_of_oscillationTarget`. -/
theorem no_off_critical_zeros_in_strip_of_oscillationTarget
    (hCA : ClassicalAnalysisAssumptions)
    (hInh : CofactorBMOInheritance)
    (hT : OscillationTarget) :
    ∀ ρ : ℂ, completedRiemannZeta ρ = 0 → ρ ∈ criticalStrip → False := by
  rcases hT with ⟨M, h_osc, hM_le⟩
  exact no_off_critical_zeros_in_strip (hCA := hCA) (hInh := hInh) M h_osc hM_le

/-- Port analogue of `Main.RiemannHypothesis_recognition_geometry`, removing `RGAssumptions`. -/
theorem RiemannHypothesis_recognition_geometry
    (hCA : ClassicalAnalysisAssumptions)
    (hInh : CofactorBMOInheritance)
    (M : ℝ) (h_osc : InBMOWithBound logAbsXi M) (hM_le : M ≤ C_tail) :
    ∀ ρ : ℂ, completedRiemannZeta ρ = 0 → ρ.re = 1/2 := by
  intro ρ hρ
  by_contra h
  cases' (ne_iff_lt_or_gt.mp h) with hlt hgt
  · -- If Re(ρ) < 1/2, use functional equation symmetry: 1-ρ is a zero with Re>1/2.
    have hρ' : completedRiemannZeta (1 - ρ) = 0 := by
      -- Mathlib: `completedRiemannZeta (1 - s) = completedRiemannZeta s`.
      simpa [completedRiemannZeta_one_sub] using hρ
    have hgt' : 1/2 < (1 - ρ).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have : False :=
      no_off_critical_zeros_in_strip (hCA := hCA) (hInh := hInh) M h_osc hM_le
        (1 - ρ) hρ' (by simpa [criticalStrip, Set.mem_setOf_eq] using hgt')
    exact this
  · -- If Re(ρ) > 1/2, contradict no-off-critical-zeros.
    have : False :=
      no_off_critical_zeros_in_strip (hCA := hCA) (hInh := hInh) M h_osc hM_le
        ρ hρ (by simpa [criticalStrip, Set.mem_setOf_eq] using hgt)
    exact this

/-- Convenience wrapper: remove the explicit inheritance argument using
`cofactorBMOInheritance_trivial`. -/
theorem no_off_critical_zeros_in_strip_trivial_inheritance
    (hCA : ClassicalAnalysisAssumptions)
    (M : ℝ) (h_osc : InBMOWithBound logAbsXi M) (hM_le : M ≤ C_tail) :
    ∀ ρ : ℂ, completedRiemannZeta ρ = 0 → ρ ∈ criticalStrip → False := by
  exact
    no_off_critical_zeros_in_strip
      (hCA := hCA) (hInh := cofactorBMOInheritance_trivial) M h_osc hM_le

/-- Convenience wrapper: remove the explicit inheritance argument using
`cofactorBMOInheritance_trivial`. -/
theorem no_off_critical_zeros_in_strip_of_oscillationTarget_trivial_inheritance
    (hCA : ClassicalAnalysisAssumptions)
    (hT : OscillationTarget) :
    ∀ ρ : ℂ, completedRiemannZeta ρ = 0 → ρ ∈ criticalStrip → False := by
  exact
    no_off_critical_zeros_in_strip_of_oscillationTarget
      (hCA := hCA) (hInh := cofactorBMOInheritance_trivial) (hT := hT)

/-- Convenience wrapper: remove the explicit inheritance argument using
`cofactorBMOInheritance_trivial`. -/
theorem RiemannHypothesis_recognition_geometry_trivial_inheritance
    (hCA : ClassicalAnalysisAssumptions)
    (M : ℝ) (h_osc : InBMOWithBound logAbsXi M) (hM_le : M ≤ C_tail) :
    ∀ ρ : ℂ, completedRiemannZeta ρ = 0 → ρ.re = 1/2 := by
  exact
    RiemannHypothesis_recognition_geometry
      (hCA := hCA) (hInh := cofactorBMOInheritance_trivial) M h_osc hM_le

/-- Convenience wrapper: Port RH theorem driven directly from `OscillationTarget`, with trivial inheritance. -/
theorem RiemannHypothesis_recognition_geometry_of_oscillationTarget_trivial_inheritance
    (hCA : ClassicalAnalysisAssumptions)
    (hT : OscillationTarget) :
    ∀ ρ : ℂ, completedRiemannZeta ρ = 0 → ρ.re = 1/2 := by
  rcases hT with ⟨M, h_osc, hM_le⟩
  exact RiemannHypothesis_recognition_geometry_trivial_inheritance (hCA := hCA) M h_osc hM_le

/-- Port analogue of `Main.no_off_critical_zeros_in_strip_of_oscillationTarget` that avoids the monolithic
`ClassicalAnalysisAssumptions` record entirely, using the explicit energy-based CR/Green targets instead. -/
theorem no_off_critical_zeros_in_strip_of_oscillationTarget_of_xi_and_cofactor_CRGreen
    (hXi : XiCRGreenAssumptions)
    (hCof : CofactorCRGreenAssumptions)
    (hT : OscillationTarget) :
    ∀ ρ : ℂ, completedRiemannZeta ρ = 0 → ρ ∈ criticalStrip → False := by
  intro ρ hρ_zero hρ_crit
  simp only [criticalStrip, Set.mem_setOf_eq] at hρ_crit
  by_cases h_re_gt_one : 1 < ρ.re
  · exact completedRiemannZeta_ne_zero_of_re_gt_one h_re_gt_one hρ_zero
  · push_neg at h_re_gt_one
    have hρ_re : 1/2 < ρ.re := hρ_crit
    exact
      Port.zero_free_with_interval_of_OscillationTarget_of_xi_and_cofactor_CRGreen
        (ρ := ρ) (hXi := hXi) (hCof := hCof)
        (hρ_re := hρ_re) (hρ_zero := hρ_zero) (hOsc := hT)

/-- Port analogue of `Main.RiemannHypothesis_recognition_geometry_of_oscillationTarget` using the explicit
energy-based CR/Green targets instead of `ClassicalAnalysisAssumptions` and `RGAssumptions`. -/
theorem RiemannHypothesis_recognition_geometry_of_oscillationTarget_of_xi_and_cofactor_CRGreen
    (hXi : XiCRGreenAssumptions)
    (hCof : CofactorCRGreenAssumptions)
    (hT : OscillationTarget) :
    ∀ ρ : ℂ, completedRiemannZeta ρ = 0 → ρ.re = 1/2 := by
  intro ρ hρ
  by_contra h
  cases' (ne_iff_lt_or_gt.mp h) with hlt hgt
  · have hρ' : completedRiemannZeta (1 - ρ) = 0 := by
      simpa [completedRiemannZeta_one_sub] using hρ
    have hgt' : 1/2 < (1 - ρ).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have : False :=
      no_off_critical_zeros_in_strip_of_oscillationTarget_of_xi_and_cofactor_CRGreen
        (hXi := hXi) (hCof := hCof) (hT := hT)
        (1 - ρ) hρ' (by simpa [criticalStrip, Set.mem_setOf_eq] using hgt')
    exact this
  · have : False :=
      no_off_critical_zeros_in_strip_of_oscillationTarget_of_xi_and_cofactor_CRGreen
        (hXi := hXi) (hCof := hCof) (hT := hT)
        ρ hρ (by simpa [criticalStrip, Set.mem_setOf_eq] using hgt)
    exact this

/-- Same as `RiemannHypothesis_recognition_geometry_of_oscillationTarget_of_xi_and_cofactor_CRGreen`, but taking
the bundled `EnergyCRGreenAssumptions`. -/
theorem RiemannHypothesis_recognition_geometry_of_oscillationTarget_of_energyCRGreenAssumptions
    (h : EnergyCRGreenAssumptions)
    (hT : OscillationTarget) :
    ∀ ρ : ℂ, completedRiemannZeta ρ = 0 → ρ.re = 1/2 := by
  exact
    RiemannHypothesis_recognition_geometry_of_oscillationTarget_of_xi_and_cofactor_CRGreen
      (hXi := h.xi) (hCof := h.cofactor) (hT := hT)

/-- Same Port RH theorem, but taking **real-valued** CR/Green targets (blueprint-style).

These imply the `Real.Angle` energy-based targets via `Port.RealPhaseTransfer`. -/
theorem RiemannHypothesis_recognition_geometry_of_oscillationTarget_of_real_CRGreen
    (hXi : XiCRGreenAssumptionsReal)
    (hCof : CofactorCRGreenAssumptionsReal)
    (hT : OscillationTarget) :
    ∀ ρ : ℂ, completedRiemannZeta ρ = 0 → ρ.re = 1/2 := by
  have hXi' : XiCRGreenAssumptions := xiCRGreenAssumptions_of_real hXi
  have hCof' : CofactorCRGreenAssumptions := cofactorCRGreenAssumptions_of_real hCof
  exact
    RiemannHypothesis_recognition_geometry_of_oscillationTarget_of_xi_and_cofactor_CRGreen
      (hXi := hXi') (hCof := hCof') (hT := hT)

/-- Same Port RH theorem, but taking the bundled **real-valued** CR/Green targets. -/
theorem RiemannHypothesis_recognition_geometry_of_oscillationTarget_of_energyCRGreenAssumptionsReal
    (h : EnergyCRGreenAssumptionsReal)
    (hT : OscillationTarget) :
    ∀ ρ : ℂ, completedRiemannZeta ρ = 0 → ρ.re = 1/2 := by
  exact
    RiemannHypothesis_recognition_geometry_of_oscillationTarget_of_real_CRGreen
      (hXi := h.xi) (hCof := h.cofactor) (hT := hT)

end Port
end RiemannRecognitionGeometry
