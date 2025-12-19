/-
# Port step: zero-free contradiction without `RGAssumptions` (centered route)

This file mirrors `Axioms.zero_free_with_interval`, but replaces the RG-specific tail machinery
(`RGAssumptions` + `Conjectures.weierstrass_tail_bound_axiom_statement`) by the Port centered
dominance theorem:

`Port.blaschke_dominates_total_centered_of_cofactorBMO`.

It still uses the *upper bound* on the total phase signal from `Axioms.totalPhaseSignal_bound`,
which depends on a BMO/oscillation certificate for `logAbsXi`.

So the resulting contradiction assumes **two** BMO certificates:
- one for `logAbsXi` (upper bound), and
- one for the cofactor boundary log-modulus `cofactorLogAbs ρ` (lower bound route).
-/

import RiemannRecognitionGeometry.Axioms
import RiemannRecognitionGeometry.Port.BlaschkeDominatesTotal
import RiemannRecognitionGeometry.Port.CofactorBMOInheritance
import RiemannRecognitionGeometry.Port.CofactorCRGreenAssumptions
import RiemannRecognitionGeometry.Port.TotalPhaseSignalBound
import RiemannRecognitionGeometry.Port.XiCRGreenAssumptions
import RiemannRecognitionGeometry.Port.EnergyCRGreenAssumptions
import RiemannRecognitionGeometry.Port.EnergyCRGreenS2
import RiemannRecognitionGeometry.Port.RealPhaseTransfer
import RiemannRecognitionGeometry.Port.EnergyCRGreenAssumptionsReal

noncomputable section

namespace RiemannRecognitionGeometry
namespace Port

open Real Complex

/-- Port version of `Axioms.zero_free_with_interval` (centered contradiction),
removing the `RGAssumptions` dependency.

Assumptions:
- `h_osc` gives the **upper bound** `totalPhaseSignal ≤ U_tail M`,
- `h_bmo` gives the **lower bound** via the centered dominance route,
- `M ≤ C_tail` closes the numeric inequality. -/
theorem zero_free_with_interval_of_cofactorBMO (ρ : ℂ)
    (hCA : ClassicalAnalysisAssumptions)
    (hρ_re : 1/2 < ρ.re)
    (hρ_zero : completedRiemannZeta ρ = 0)
    (M : ℝ)
    (h_osc : InBMOWithBound logAbsXi M)
    (h_bmo : InBMOWithBound (cofactorLogAbs ρ) M)
    (hM_le : M ≤ C_tail) :
    False := by
  -- Lower bound comes directly from the Port centered dominance theorem.
  have h_dominance :=
    blaschke_dominates_total_centered_of_cofactorBMO (ρ := ρ) (hCA := hCA)
      (hρ_zero := hρ_zero) (M := M) (h_bmo := h_bmo) (hρ_re := hρ_re)

  -- Extract the internal interval `I0` from the `let`-bound statement.
  set d : ℝ := ρ.re - 1/2 with hd_def
  have h_d_pos : d > 0 := by simp [hd_def]; linarith
  set I0 : WhitneyInterval := { t0 := ρ.im, len := 2 * d, len_pos := by nlinarith } with hI0_def

  -- Upper bound: totalPhaseSignal I0 ≤ U_tail M (Carleson/BMO bound for `logAbsXi`)
  have h_carleson := totalPhaseSignal_bound I0 hCA M h_osc

  -- Numeric closure: `L_rec > 2 * U_tail M` from `M ≤ C_tail`.
  have h_l_rec_large : L_rec > 2 * U_tail M := by
    have hM_nonneg : 0 ≤ M := le_of_lt h_osc.1
    have hmono : U_tail M ≤ U_tail C_tail := U_tail_mono hM_nonneg hM_le
    have hclose : (2 * U_tail C_tail) < L_rec := zero_free_condition_C_tail
    have h2mono : (2 * U_tail M) ≤ (2 * U_tail C_tail) := by nlinarith
    have : (2 * U_tail M) < L_rec := lt_of_le_of_lt h2mono hclose
    linarith

  -- Contradiction:
  -- h_dominance (specialized to I0): totalPhaseSignal I0 ≥ L_rec - U_tail M
  -- h_carleson: totalPhaseSignal I0 ≤ U_tail M
  -- and `L_rec - U_tail M > U_tail M`.
  have h_dom_I0 : totalPhaseSignal I0 ≥ L_rec - U_tail M := by
    -- specialize the `let`-bound statement
    simpa [hd_def, hI0_def] using h_dominance
  linarith

/-- Port version of the centered contradiction, but with the cofactor BMO certificate produced
from the `logAbsXi` certificate via an explicit inheritance interface. -/
theorem zero_free_with_interval_of_inheritance (ρ : ℂ)
    (hCA : ClassicalAnalysisAssumptions)
    (hInh : CofactorBMOInheritance)
    (hρ_re : 1/2 < ρ.re)
    (hρ_zero : completedRiemannZeta ρ = 0)
    (M : ℝ)
    (h_osc : InBMOWithBound logAbsXi M)
    (hM_le : M ≤ C_tail) :
    False := by
  have h_bmo : InBMOWithBound (cofactorLogAbs ρ) M :=
    hInh.cofactor_bmo_of_logAbsXi_bmo ρ M hρ_re h_osc
  exact
    zero_free_with_interval_of_cofactorBMO
      (ρ := ρ) (hCA := hCA)
      (hρ_re := hρ_re) (hρ_zero := hρ_zero)
      (M := M) (h_osc := h_osc) (h_bmo := h_bmo) (hM_le := hM_le)

/-- Port version of the centered contradiction driven directly by `OscillationTarget`,
plus an explicit cofactor BMO inheritance interface. -/
theorem zero_free_with_interval_of_OscillationTarget_and_inheritance (ρ : ℂ)
    (hCA : ClassicalAnalysisAssumptions)
    (hInh : CofactorBMOInheritance)
    (hρ_re : 1/2 < ρ.re)
    (hρ_zero : completedRiemannZeta ρ = 0)
    (hOsc : OscillationTarget) :
    False := by
  rcases hOsc with ⟨M, h_osc, hM_le⟩
  exact zero_free_with_interval_of_inheritance
    (ρ := ρ) (hCA := hCA) (hInh := hInh)
    (hρ_re := hρ_re) (hρ_zero := hρ_zero)
    (M := M) (h_osc := h_osc) (hM_le := hM_le)

/-- Convenience wrapper: with the current Port model, cofactor BMO inheritance is definitionally trivial,
so the centered contradiction can be driven directly from `OscillationTarget` without extra inputs. -/
theorem zero_free_with_interval_of_OscillationTarget (ρ : ℂ)
    (hCA : ClassicalAnalysisAssumptions)
    (hρ_re : 1/2 < ρ.re)
    (hρ_zero : completedRiemannZeta ρ = 0)
    (hOsc : OscillationTarget) :
    False := by
  exact
    zero_free_with_interval_of_OscillationTarget_and_inheritance
      (ρ := ρ) (hCA := hCA) (hInh := cofactorBMOInheritance_trivial)
      (hρ_re := hρ_re) (hρ_zero := hρ_zero) (hOsc := hOsc)

/-- Energy-based Port centered contradiction:

This version removes `ClassicalAnalysisAssumptions` entirely, replacing it with the two explicit
energy-based CR/Green targets:

- `XiCRGreenAssumptions`: upper bound `totalPhaseSignal I ≤ U_tail M`, and
- `CofactorCRGreenAssumptions`: lower bound via the Port tail bound route.
-/
theorem zero_free_with_interval_of_OscillationTarget_of_xi_and_cofactor_CRGreen (ρ : ℂ)
    (hXi : XiCRGreenAssumptions)
    (hCof : CofactorCRGreenAssumptions)
    (hρ_re : 1/2 < ρ.re)
    (hρ_zero : completedRiemannZeta ρ = 0)
    (hOsc : OscillationTarget) :
    False := by
  rcases hOsc with ⟨M, h_osc, hM_le⟩

  -- Cofactor BMO is definitionally the same as the `logAbsXi` BMO certificate in the current Port model.
  have h_bmo : InBMOWithBound (cofactorLogAbs ρ) M := by
    simpa [cofactorLogAbs] using h_osc

  -- Lower bound from centered dominance using the energy-based cofactor CR/Green target.
  have h_dominance :=
    blaschke_dominates_total_centered_of_cofactorBMO_of_cofactorCRGreenAssumptions
      (ρ := ρ) (hGreen := hCof) (hρ_zero := hρ_zero)
      (M := M) (h_bmo := h_bmo) (hρ_re := hρ_re)

  -- Extract the internal centered interval `I0`.
  set d : ℝ := ρ.re - 1/2 with hd_def
  have hd_pos : 0 < d := by
    -- `d = ρ.re - 1/2` and `hρ_re : 1/2 < ρ.re`.
    have : 0 < ρ.re - 1/2 := by linarith
    simpa [hd_def] using this
  set I0 : WhitneyInterval :=
      { t0 := ρ.im
        len := 2 * d
        len_pos := by nlinarith [hd_pos] } with hI0_def

  have h_dom_I0 : totalPhaseSignal I0 ≥ L_rec - U_tail M := by
    simpa [hd_def, hI0_def] using h_dominance

  -- Upper bound from the energy-based xi CR/Green target.
  have h_upper : totalPhaseSignal I0 ≤ U_tail M :=
    totalPhaseSignal_bound_of_xiCRGreenAssumptions (I := I0) (hXi := hXi) (M := M) h_osc

  -- Numeric closure: `L_rec > 2 * U_tail M` from `M ≤ C_tail`.
  have h_l_rec_large : L_rec > 2 * U_tail M := by
    have hM_nonneg : 0 ≤ M := le_of_lt h_osc.1
    have hmono : U_tail M ≤ U_tail C_tail := U_tail_mono hM_nonneg hM_le
    have hclose : (2 * U_tail C_tail) < L_rec := zero_free_condition_C_tail
    have h2mono : (2 * U_tail M) ≤ (2 * U_tail C_tail) := by nlinarith
    have : (2 * U_tail M) < L_rec := lt_of_le_of_lt h2mono hclose
    linarith

  -- Contradiction: lower bound vs upper bound.
  linarith

/-- Same as `zero_free_with_interval_of_OscillationTarget_of_xi_and_cofactor_CRGreen`, but taking the bundled
`EnergyCRGreenAssumptions`. -/
theorem zero_free_with_interval_of_OscillationTarget_of_energyCRGreenAssumptions (ρ : ℂ)
    (h : EnergyCRGreenAssumptions)
    (hρ_re : 1/2 < ρ.re)
    (hρ_zero : completedRiemannZeta ρ = 0)
    (hOsc : OscillationTarget) :
    False := by
  exact
    zero_free_with_interval_of_OscillationTarget_of_xi_and_cofactor_CRGreen
      (ρ := ρ) (hXi := h.xi) (hCof := h.cofactor)
      (hρ_re := hρ_re) (hρ_zero := hρ_zero) (hOsc := hOsc)

/-- Strong version of the Port centered contradiction, taking the faithful **strong**
energy-form CR/Green targets. -/
theorem zero_free_with_interval_of_OscillationTarget_of_energyCRGreenAssumptionsStrong (ρ : ℂ)
    (h : EnergyCRGreenAssumptionsStrong)
    (hρ_re : 1/2 < ρ.re)
    (hρ_zero : completedRiemannZeta ρ = 0)
    (hOsc : OscillationTarget) :
    False :=
  zero_free_with_interval_of_OscillationTarget_of_energyCRGreenAssumptions
    (ρ := ρ) (h := energyCRGreenAssumptions_of_strong h)
    (hρ_re := hρ_re) (hρ_zero := hρ_zero) (hOsc := hOsc)

/-- Same centered contradiction, but taking **real-valued** CR/Green targets (blueprint-style).

These imply the `Real.Angle` energy-based targets via `Port.RealPhaseTransfer`. -/
theorem zero_free_with_interval_of_OscillationTarget_of_real_CRGreen (ρ : ℂ)
    (hXi : XiCRGreenAssumptionsReal)
    (hCof : CofactorCRGreenAssumptionsReal)
    (hρ_re : 1/2 < ρ.re)
    (hρ_zero : completedRiemannZeta ρ = 0)
    (hOsc : OscillationTarget) :
    False := by
  have hXi' : XiCRGreenAssumptions := xiCRGreenAssumptions_of_real hXi
  have hCof' : CofactorCRGreenAssumptions := cofactorCRGreenAssumptions_of_real hCof
  exact
    zero_free_with_interval_of_OscillationTarget_of_xi_and_cofactor_CRGreen
      (ρ := ρ) (hXi := hXi') (hCof := hCof')
      (hρ_re := hρ_re) (hρ_zero := hρ_zero) (hOsc := hOsc)

/-- Same centered contradiction, but taking the bundled **real-valued** CR/Green targets. -/
theorem zero_free_with_interval_of_OscillationTarget_of_energyCRGreenAssumptionsReal (ρ : ℂ)
    (h : EnergyCRGreenAssumptionsReal)
    (hρ_re : 1/2 < ρ.re)
    (hρ_zero : completedRiemannZeta ρ = 0)
    (hOsc : OscillationTarget) :
    False := by
  exact
    zero_free_with_interval_of_OscillationTarget_of_real_CRGreen
      (ρ := ρ) (hXi := h.xi) (hCof := h.cofactor)
      (hρ_re := hρ_re) (hρ_zero := hρ_zero) (hOsc := hOsc)

/-- Same centered contradiction, but taking the faithful S2 assumptions (trace identity + pairing bound)
on both the xi side and the cofactor side. -/
theorem zero_free_with_interval_of_OscillationTarget_of_S2 (ρ : ℂ)
    (hXi : XiCRGreenS2.Assumptions)
    (hCof : CofactorCRGreenS2.Assumptions)
    (hρ_re : 1/2 < ρ.re)
    (hρ_zero : completedRiemannZeta ρ = 0)
    (hOsc : OscillationTarget) :
    False := by
  have h' : EnergyCRGreenAssumptions :=
    energyCRGreenAssumptions_of_S2 hXi hCof
  exact
    zero_free_with_interval_of_OscillationTarget_of_energyCRGreenAssumptions
      (ρ := ρ) (h := h') (hρ_re := hρ_re) (hρ_zero := hρ_zero) (hOsc := hOsc)

end Port
end RiemannRecognitionGeometry
