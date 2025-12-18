import RiemannRecognitionGeometry.ExplicitFormula.PPlusCore
import RiemannRecognitionGeometry.ExplicitFormula.ZetaInstantiation

/-!
# (P+) for the concrete ζ PSC ratio

This file connects the generic `(P+)` predicate in `PPlusCore.lean` to the concrete
ζ PSC ratio in `ZetaInstantiation.lean`.

Key point:
`ZetaPSCHypotheses.boundaryPhase_repr` already gives the a.e. boundary phase representation

`J(boundary t) = exp(i·θ(t))`

so `(P+)` becomes exactly `cos(θ(t)) ≥ 0` a.e. via `PPlusCore.PPlus_holds_iff_cos_nonneg_of_phase`.

This isolates the remaining “phase argument” as a single analytic statement:

`∀ᵐ t, 0 ≤ Real.cos (boundaryPhase t)`.
-/

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula
namespace ZetaInstantiation

open Complex MeasureTheory Filter
open scoped Real

/-- The concrete pinch PSC ratio on the boundary for ζ (det2/outer/ξ). -/
def J_pinch_zeta : ℂ → ℂ :=
  OuterConstruction.J_pinch det2_zeta outer_zeta xi_zeta

/-- `(P+)` for the ζ pinch field (boundary real-part nonnegativity a.e.). -/
def PPlus_zeta : Prop :=
  PPlusCore.PPlus_holds det2_zeta outer_zeta xi_zeta

/--
Using the phase representation hypothesis, `(P+)` is equivalent to `cos(θ) ≥ 0` a.e.

This is the core “phase positivity” target.
-/
theorem PPlus_zeta_iff_cos_nonneg (H : ZetaPSCHypotheses) :
    PPlus_zeta ↔ (∀ᵐ t : ℝ, 0 ≤ Real.cos (H.boundaryPhase t)) := by
  -- Apply the generic equivalence with θ := H.boundaryPhase.
  -- First, rewrite the phase representation into the `J_pinch` form expected by `PPlusCore`.
  have hPhase :
      ∀ᵐ t : ℝ,
        OuterConstruction.J_pinch det2_zeta outer_zeta xi_zeta (OuterConstruction.boundary t) =
          Complex.exp (Complex.I * (H.boundaryPhase t : ℂ)) := by
    -- H.boundaryPhase_repr is stated at `1/2 + I*t` and with explicit det2/outer/xi;
    -- this is definitional equal to `OC.boundary t` and `OC.J_pinch ...`.
    -- Avoid `simp` cancellations; just unfold `OC.J_pinch` and rewrite.
    simpa [J_pinch_zeta, OuterConstruction.J_pinch, det2_zeta, outer_zeta, xi_zeta, OuterConstruction.boundary]
      using H.boundaryPhase_repr
  -- Now invoke the generic lemma.
  simpa [PPlus_zeta, PPlusCore.PPlus_holds] using
    (PPlusCore.PPlus_holds_iff_cos_nonneg_of_phase det2_zeta outer_zeta xi_zeta H.boundaryPhase hPhase)

/-- Sufficient condition for `(P+)` from a.e. cosine nonnegativity of the boundary phase. -/
theorem PPlus_zeta_of_cos_nonneg (H : ZetaPSCHypotheses)
    (hcos : ∀ᵐ t : ℝ, 0 ≤ Real.cos (H.boundaryPhase t)) :
    PPlus_zeta := by
  exact (PPlus_zeta_iff_cos_nonneg H).2 hcos

end ZetaInstantiation
end ExplicitFormula
end RiemannRecognitionGeometry
