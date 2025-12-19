/-
# Port step: local zero-free (band interior) without `RGAssumptions`

This file mirrors the RG theorem `Axioms.local_zero_free`, but replaces the call to
`Axioms.zero_free_with_interval` (which depends on `RGAssumptions`) by the Port theorem
`Port.zero_free_with_interval_of_inheritance`.

This file now supports three “assumption surfaces” (all build-green):

- **Compatibility route**: `ClassicalAnalysisAssumptions` (+ the inheritance shim, now trivial in the
  current Port model).
- **Energy-based route**: explicit CR/Green targets `XiCRGreenAssumptions` + `CofactorCRGreenAssumptions`
  (or their bundles), avoiding the monolithic `ClassicalAnalysisAssumptions` record.
- **Faithful S2 route**: trace identity + pairing bound on both sides (`XiCRGreenS2.Assumptions` +
  `CofactorCRGreenS2.Assumptions`), matching the blueprint decomposition.
-/

import RiemannRecognitionGeometry.Axioms
import RiemannRecognitionGeometry.Port.ZeroFreeWithInterval

noncomputable section

namespace RiemannRecognitionGeometry
namespace Port

open Complex Set

/-- Port analogue of `Axioms.local_zero_free` removing the `RGAssumptions` parameter,
using `Port.zero_free_with_interval_of_inheritance`. -/
theorem local_zero_free_of_inheritance (I : WhitneyInterval) (B : RecognizerBand)
    (hB_base : B.base = I)
    (ρ : ℂ) (hρ_interior : ρ ∈ B.interior)
    (hρ_zero : completedRiemannZeta ρ = 0)
    (hρ_re_upper : ρ.re ≤ 1)  -- Critical strip constraint
    (h_width_lower : 2 * I.len ≥ |ρ.im|)   -- Lower bound: interval width ≥ |γ|
    (h_width_upper : 2 * I.len ≤ 10 * |ρ.im|)  -- Upper bound
    (hCA : ClassicalAnalysisAssumptions)
    (hInh : CofactorBMOInheritance)
    (M : ℝ) (h_osc : InBMOWithBound logAbsXi M)
    (hM_le : M ≤ C_tail) :
    False := by
  simp only [RecognizerBand.interior, Set.mem_setOf_eq] at hρ_interior
  obtain ⟨hσ_lower, hσ_upper, hγ_in⟩ := hρ_interior

  have hρ_re : 1/2 < ρ.re := by
    have h := B.σ_lower_gt_half
    have hpos := B.thickness_pos
    linarith

  -- Invoke the centered contradiction (no `RGAssumptions`)
  exact
    zero_free_with_interval_of_inheritance
      (ρ := ρ) (hCA := hCA) (hInh := hInh)
      (hρ_re := hρ_re) (hρ_zero := hρ_zero)
      (M := M) (h_osc := h_osc) (hM_le := hM_le)

/-- Convenience wrapper: drive the Port local-zero-free step directly from `OscillationTarget`
using the trivial cofactor BMO inheritance for the current Port model. -/
theorem local_zero_free_of_OscillationTarget (I : WhitneyInterval) (B : RecognizerBand)
    (hB_base : B.base = I)
    (ρ : ℂ) (hρ_interior : ρ ∈ B.interior)
    (hρ_zero : completedRiemannZeta ρ = 0)
    (hρ_re_upper : ρ.re ≤ 1)
    (h_width_lower : 2 * I.len ≥ |ρ.im|)
    (h_width_upper : 2 * I.len ≤ 10 * |ρ.im|)
    (hCA : ClassicalAnalysisAssumptions)
    (hOsc : OscillationTarget) :
    False := by
  rcases hOsc with ⟨M, h_osc, hM_le⟩
  exact
    local_zero_free_of_inheritance I B hB_base ρ hρ_interior hρ_zero hρ_re_upper h_width_lower h_width_upper
      hCA cofactorBMOInheritance_trivial M h_osc hM_le

/-- Port analogue of `Axioms.no_interior_zeros` removing the `RGAssumptions` parameter. -/
theorem no_interior_zeros_of_inheritance (I : WhitneyInterval) (B : RecognizerBand)
    (hB_base : B.base = I)
    (hCA : ClassicalAnalysisAssumptions)
    (hInh : CofactorBMOInheritance)
    (M : ℝ) (h_osc : InBMOWithBound logAbsXi M)
    (hM_le : M ≤ C_tail) :
    ∀ ρ ∈ B.interior, ρ.re ≤ 1 → (2 * I.len ≥ |ρ.im|) → (2 * I.len ≤ 10 * |ρ.im|) →
      completedRiemannZeta ρ ≠ 0 := by
  intro ρ hρ_interior hρ_re_upper h_width_lower h_width_upper hρ_zero
  exact
    (local_zero_free_of_inheritance I B hB_base ρ hρ_interior hρ_zero hρ_re_upper h_width_lower
        h_width_upper hCA hInh M h_osc hM_le).elim

/-- Energy-based Port local-zero-free: drive the contradiction from the explicit CR/Green targets,
avoiding `ClassicalAnalysisAssumptions`. -/
theorem local_zero_free_of_OscillationTarget_of_xi_and_cofactor_CRGreen
    (I : WhitneyInterval) (B : RecognizerBand)
    (hB_base : B.base = I)
    (ρ : ℂ) (hρ_interior : ρ ∈ B.interior)
    (hρ_zero : completedRiemannZeta ρ = 0)
    (hρ_re_upper : ρ.re ≤ 1)
    (h_width_lower : 2 * I.len ≥ |ρ.im|)
    (h_width_upper : 2 * I.len ≤ 10 * |ρ.im|)
    (hXi : XiCRGreenAssumptions)
    (hCof : CofactorCRGreenAssumptions)
    (hOsc : OscillationTarget) :
    False := by
  simp only [RecognizerBand.interior, Set.mem_setOf_eq] at hρ_interior
  obtain ⟨_hσ_lower, _hσ_upper, _hγ_in⟩ := hρ_interior
  have hρ_re : 1/2 < ρ.re := by
    have h := B.σ_lower_gt_half
    have hpos := B.thickness_pos
    linarith
  exact
    zero_free_with_interval_of_OscillationTarget_of_xi_and_cofactor_CRGreen
      (ρ := ρ) (hXi := hXi) (hCof := hCof)
      (hρ_re := hρ_re) (hρ_zero := hρ_zero) (hOsc := hOsc)

/-- Same as `local_zero_free_of_OscillationTarget_of_xi_and_cofactor_CRGreen`, but taking the bundled
`EnergyCRGreenAssumptions`. -/
theorem local_zero_free_of_OscillationTarget_of_energyCRGreenAssumptions
    (I : WhitneyInterval) (B : RecognizerBand)
    (hB_base : B.base = I)
    (ρ : ℂ) (hρ_interior : ρ ∈ B.interior)
    (hρ_zero : completedRiemannZeta ρ = 0)
    (hρ_re_upper : ρ.re ≤ 1)
    (h_width_lower : 2 * I.len ≥ |ρ.im|)
    (h_width_upper : 2 * I.len ≤ 10 * |ρ.im|)
    (h : EnergyCRGreenAssumptions)
    (hOsc : OscillationTarget) :
    False := by
  exact
    local_zero_free_of_OscillationTarget_of_xi_and_cofactor_CRGreen
      (I := I) (B := B) (hB_base := hB_base)
      (ρ := ρ) (hρ_interior := hρ_interior) (hρ_zero := hρ_zero)
      (hρ_re_upper := hρ_re_upper) (h_width_lower := h_width_lower) (h_width_upper := h_width_upper)
      (hXi := h.xi) (hCof := h.cofactor) (hOsc := hOsc)

/-- Same local-zero-free step, but driven by the faithful S2 assumptions (trace identity + pairing bound)
on both the xi side and the cofactor side. -/
theorem local_zero_free_of_OscillationTarget_of_S2
    (I : WhitneyInterval) (B : RecognizerBand)
    (hB_base : B.base = I)
    (ρ : ℂ) (hρ_interior : ρ ∈ B.interior)
    (hρ_zero : completedRiemannZeta ρ = 0)
    (hρ_re_upper : ρ.re ≤ 1)
    (h_width_lower : 2 * I.len ≥ |ρ.im|)
    (h_width_upper : 2 * I.len ≤ 10 * |ρ.im|)
    (hXi : XiCRGreenS2.Assumptions)
    (hCof : CofactorCRGreenS2.Assumptions)
    (hOsc : OscillationTarget) :
    False := by
  simp only [RecognizerBand.interior, Set.mem_setOf_eq] at hρ_interior
  obtain ⟨_hσ_lower, _hσ_upper, _hγ_in⟩ := hρ_interior
  have hρ_re : 1/2 < ρ.re := by
    have h := B.σ_lower_gt_half
    have hpos := B.thickness_pos
    linarith
  exact
    zero_free_with_interval_of_OscillationTarget_of_S2
      (ρ := ρ) (hXi := hXi) (hCof := hCof)
      (hρ_re := hρ_re) (hρ_zero := hρ_zero) (hOsc := hOsc)

/-- Energy-based Port analogue of `no_interior_zeros`, avoiding `ClassicalAnalysisAssumptions`. -/
theorem no_interior_zeros_of_OscillationTarget_of_xi_and_cofactor_CRGreen
    (I : WhitneyInterval) (B : RecognizerBand)
    (hB_base : B.base = I)
    (hXi : XiCRGreenAssumptions)
    (hCof : CofactorCRGreenAssumptions)
    (hOsc : OscillationTarget) :
    ∀ ρ ∈ B.interior, ρ.re ≤ 1 → (2 * I.len ≥ |ρ.im|) → (2 * I.len ≤ 10 * |ρ.im|) →
      completedRiemannZeta ρ ≠ 0 := by
  intro ρ hρ_interior hρ_re_upper h_width_lower h_width_upper hρ_zero
  exact
    (local_zero_free_of_OscillationTarget_of_xi_and_cofactor_CRGreen
      (I := I) (B := B) (hB_base := hB_base)
      (ρ := ρ) (hρ_interior := hρ_interior) (hρ_zero := hρ_zero)
      (hρ_re_upper := hρ_re_upper) (h_width_lower := h_width_lower) (h_width_upper := h_width_upper)
      (hXi := hXi) (hCof := hCof) (hOsc := hOsc)).elim

/-- Same as `no_interior_zeros_of_OscillationTarget_of_xi_and_cofactor_CRGreen`, but taking the bundled
`EnergyCRGreenAssumptions`. -/
theorem no_interior_zeros_of_OscillationTarget_of_energyCRGreenAssumptions
    (I : WhitneyInterval) (B : RecognizerBand)
    (hB_base : B.base = I)
    (h : EnergyCRGreenAssumptions)
    (hOsc : OscillationTarget) :
    ∀ ρ ∈ B.interior, ρ.re ≤ 1 → (2 * I.len ≥ |ρ.im|) → (2 * I.len ≤ 10 * |ρ.im|) →
      completedRiemannZeta ρ ≠ 0 := by
  exact
    no_interior_zeros_of_OscillationTarget_of_xi_and_cofactor_CRGreen
      (I := I) (B := B) (hB_base := hB_base)
      (hXi := h.xi) (hCof := h.cofactor) (hOsc := hOsc)

/-- Same interior-zero-free statement, but driven by the faithful S2 assumptions. -/
theorem no_interior_zeros_of_OscillationTarget_of_S2
    (I : WhitneyInterval) (B : RecognizerBand)
    (hB_base : B.base = I)
    (hXi : XiCRGreenS2.Assumptions)
    (hCof : CofactorCRGreenS2.Assumptions)
    (hOsc : OscillationTarget) :
    ∀ ρ ∈ B.interior, ρ.re ≤ 1 → (2 * I.len ≥ |ρ.im|) → (2 * I.len ≤ 10 * |ρ.im|) →
      completedRiemannZeta ρ ≠ 0 := by
  intro ρ hρ_interior hρ_re_upper h_width_lower h_width_upper hρ_zero
  exact
    (local_zero_free_of_OscillationTarget_of_S2
      (I := I) (B := B) (hB_base := hB_base)
      (ρ := ρ) (hρ_interior := hρ_interior) (hρ_zero := hρ_zero)
      (hρ_re_upper := hρ_re_upper) (h_width_lower := h_width_lower) (h_width_upper := h_width_upper)
      (hXi := hXi) (hCof := hCof) (hOsc := hOsc)).elim

end Port
end RiemannRecognitionGeometry
