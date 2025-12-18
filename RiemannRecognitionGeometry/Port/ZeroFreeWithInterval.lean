/-!
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

end Port
end RiemannRecognitionGeometry
