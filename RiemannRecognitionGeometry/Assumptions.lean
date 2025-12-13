/-
Bundled assumptions used by the main theorems.

Goal: make dependencies explicit at the theorem signatures.

We separate:
- **Classical analysis assumptions** (expected true in standard analysis): e.g. Green/Cauchy–Schwarz.
- **RG-specific assumptions** (the bottleneck estimate(s) of the Recognition Geometry approach): e.g. the
  Weierstrass/Hadamard tail bound.

This file is intentionally lightweight: it packages existing statement-shapes without changing any proofs.
-/

import RiemannRecognitionGeometry.Phase
import RiemannRecognitionGeometry.DirichletEta

noncomputable section

open Real Complex Set MeasureTheory

namespace RiemannRecognitionGeometry

/-- Classical analysis assumptions used by the RG main chain. -/
structure ClassicalAnalysisAssumptions : Prop where
  /-- Green–Cauchy–Schwarz (phase change bounded by Carleson energy). -/
  green_identity_axiom_statement :
    ∀ (J : WhitneyInterval) (C : ℝ) (hC_pos : C > 0)
      (E : ℝ) (hE_pos : E > 0) (hE_le : E ≤ C),
      xiPhaseChange J ≤
        C_geom * Real.sqrt (E * (2 * J.len)) * (1 / Real.sqrt (2 * J.len))

  /-- ζ(s) ≠ 0 for real `s ∈ (0, 1)`. (Used to rule out real zeros when `Im ρ = 0`.) -/
  zeta_ne_zero_of_real_in_unit_interval :
    ∀ s : ℝ, 0 < s → s < 1 → riemannZeta (s : ℂ) ≠ 0

/-- RG-specific bottleneck assumptions (not known to be true unconditionally). -/
structure RGAssumptions : Prop where
  /-- Weierstrass/Hadamard tail bound: isolate a zero’s Blaschke contribution and bound the remainder. -/
  weierstrass_tail_bound_axiom_statement :
    ∀ (I : WhitneyInterval) (ρ : ℂ) (M : ℝ),
      completedRiemannZeta ρ = 0 → ρ.im ∈ I.interval →
      let d : ℝ := ρ.re - 1/2
      let y_hi : ℝ := I.t0 + I.len - ρ.im
      let y_lo : ℝ := I.t0 - I.len - ρ.im
      let blaschke := Real.arctan (y_lo / d) - Real.arctan (y_hi / d)
      ‖xiPhaseChangeAngle I - (blaschke : Real.Angle)‖ ≤ U_tail M

/-- A single packaged hypothesis expressing “BMO/oscillation is small enough to close RG”. -/
def OscillationTarget : Prop :=
  ∃ M : ℝ, InBMOWithBound logAbsXi M ∧ M ≤ C_tail

/-- Oscillation/BMO smallness target needed to close the numeric contradiction.

This is the project’s current “unconditional bottleneck”: proving (or otherwise justifying)
that `logAbsXi` admits a *small enough* mean-oscillation bound.
-/
structure OscillationAssumptions : Prop where
  /-- There exists an explicit oscillation bound `M` with `M ≤ C_tail`. -/
  oscillationTarget : OscillationTarget

end RiemannRecognitionGeometry
