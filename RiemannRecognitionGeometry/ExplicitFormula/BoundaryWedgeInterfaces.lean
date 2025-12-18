import RiemannRecognitionGeometry.Basic
import RiemannRecognitionGeometry.ExplicitFormula.PPlusZeta

/-!
# Boundary wedge chain (interfaces)

This file is the **mined interface** of the `riemann-finish` boundary‑wedge pipeline
(`rh/RS/BoundaryWedgeProof.lean`), stripped down to the smallest set of *named*
assumptions that imply the phase‑positivity target:

`∀ᵐ t, 0 ≤ cos(θ(t))`.

We keep the decomposition into three conceptual steps:

1. **Lower bound** (phase–velocity / Poisson plateau):
   `c0 * poisson_balayage(I) ≤ |windowed_phase(I)|`.

2. **Upper bound** (CR‑Green + Carleson/zero‑density):
   `|windowed_phase(I)| ≤ Cψ * sqrt(Kξ * (2*I.len))`.

3. **Whitney upgrade** (covering + identification of the boundary integrand):
   wedge bounds on all intervals ⇒ a.e. boundary positivity `(P+)`.

Once `(P+)` is available for the ζ pinch field, `PPlusZeta.lean` converts it into the
equivalent `cos(boundaryPhase) ≥ 0` a.e. (using the already‑assumed boundary phase representation).

As we port more of `riemann-finish`, we can replace these interface fields with actual proofs
piece‑by‑piece, without changing downstream code.
-/

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open Real MeasureTheory
open scoped Real

namespace ZetaInstantiation

/-- Minimal boundary‑wedge assumptions needed to derive `(P+)` for the ζ pinch field. -/
structure BoundaryWedgeAssumptions (H : ZetaPSCHypotheses) where
  /-- Paper constant c₀ (Poisson plateau constant). -/
  c0 : ℝ
  /-- Window constant Cψ^(H¹). -/
  Cψ : ℝ
  /-- Whitney/Carleson energy budget constant Kξ. -/
  Kξ : ℝ

  /-- Poisson balayage / harmonic measure of the Whitney base interval. -/
  poisson_balayage : WhitneyInterval → ℝ
  /-- Windowed phase integral on the Whitney base interval. -/
  windowed_phase : WhitneyInterval → ℝ

  /-- Phase–velocity lower bound (Poisson plateau). -/
  phase_velocity_lower_bound :
    ∀ I : WhitneyInterval, c0 * poisson_balayage I ≤ |windowed_phase I|

  /-- CR‑Green/Carleson upper bound on the windowed phase. -/
  whitney_phase_upper_bound :
    ∀ I : WhitneyInterval, |windowed_phase I| ≤ Cψ * Real.sqrt (Kξ * (2 * I.len))

  /-- Whitney covering + transport step:
      If the wedge inequality holds on all Whitney intervals, then `(P+)` holds a.e.
      for the ζ pinch field. -/
  whitney_to_PPlus_zeta :
    (∀ I : WhitneyInterval,
        c0 * poisson_balayage I ≤ Cψ * Real.sqrt (Kξ * (2 * I.len)))
      → PPlus_zeta

/-- Combine the lower and upper bounds into the wedge inequality on all Whitney intervals. -/
theorem wedge_holds_on_whitney (H : ZetaPSCHypotheses) (A : BoundaryWedgeAssumptions H) :
    ∀ I : WhitneyInterval,
      A.c0 * A.poisson_balayage I ≤ A.Cψ * Real.sqrt (A.Kξ * (2 * I.len)) := by
  intro I
  exact le_trans (A.phase_velocity_lower_bound I) (A.whitney_phase_upper_bound I)

/-- From the boundary‑wedge assumptions, deduce `(P+)` for the ζ pinch field. -/
theorem PPlus_zeta_of_boundary_wedge (H : ZetaPSCHypotheses) (A : BoundaryWedgeAssumptions H) :
    PPlus_zeta := by
  exact A.whitney_to_PPlus_zeta (wedge_holds_on_whitney H A)

/-- From the boundary‑wedge assumptions, deduce the phase‑positivity target:
`cos(boundaryPhase) ≥ 0` a.e. -/
theorem boundaryPhase_cos_nonneg_ae_of_boundary_wedge
    (H : ZetaPSCHypotheses) (A : BoundaryWedgeAssumptions H) :
    (∀ᵐ t : ℝ, 0 ≤ Real.cos (H.boundaryPhase t)) := by
  -- Use the already‑proved reduction `(P+) ↔ cos(θ) ≥ 0` for ζ.
  have hP : PPlus_zeta := PPlus_zeta_of_boundary_wedge H A
  exact (PPlus_zeta_iff_cos_nonneg H).1 hP

end ZetaInstantiation

end ExplicitFormula
end RiemannRecognitionGeometry
