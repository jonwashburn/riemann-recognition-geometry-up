import RiemannRecognitionGeometry.Port.CofactorCRGreenS2Interfaces

noncomputable section

namespace RiemannRecognitionGeometry
namespace Port

open Real Complex MeasureTheory

namespace CRBoundaryTraceInterfaces

open CofactorCRGreenS2Interfaces

/-!
# Port scaffold: CR boundary-trace interface (log-branch style)

This file is the Lean-facing counterpart of the paper lemma
`Lemma~\ref{lem:cr_boundary_trace_log}` in `recognition-geometry-dec-18.tex`.

The mathematical content is the standard Cauchy–Riemann boundary identity for a holomorphic,
nonvanishing function `f` with a holomorphic logarithm branch `F = log f`:

`∂x(Im F) = -∂y(Re F)` in the upper half-plane, and (under appropriate boundary regularity)
`d/dt v(t) = -∂y u(t,0^+)` on the boundary.

We do **not** attempt to formalize the analytic prerequisites here (Hardy boundary limits,
distributional traces, etc.). Instead we package the *exact interface shape* needed by the RG
CR/Green pipeline so that proofs can be swapped in piece-by-piece later.
-/

/--
`CRBoundaryTraceLog` is a statement-only interface for the CR boundary identity

`θ'(t) = -∂y u(t,0^+)`

where:
- `θ` is a real-valued lift of a boundary phase (mod `2π`),
- `u` is the real part of a log branch (`u = Re log f`) on the upper half-plane.

We encode `∂y u` by providing a 2D gradient-like field `gradU` and reading its second component.
-/
structure CRBoundaryTraceLog (L : CofactorPhaseLift) (F : PhaseVelocityFTC L) where
  /-- A 2D “gradient field” for the harmonic real part `u` on the upper half-plane model. -/
  gradU : WhitneyInterval → ℂ → (ℝ × ℝ → ℝ × ℝ)

  /-- Boundary CR identity: `θ' = -∂y u` on the Whitney base, in the chosen model. -/
  phaseVel_eq_neg_dy :
    ∀ (I : WhitneyInterval) (ρ : ℂ) (t : ℝ),
      t ∈ Set.uIcc (I.t0 - I.len) (I.t0 + I.len) →
        F.dPhase I ρ t = - (gradU I ρ (t, 0)).2

/-- The CR boundary-trace interface implies the Port-level `PhaseVelocityBoundaryTrace` hook,
by taking as “trace field” the function `p ↦ (-∂y u(p), 0)`. -/
def phaseVelocityBoundaryTrace_of_CRBoundaryTraceLog
    {L : CofactorPhaseLift} {F : PhaseVelocityFTC L} (h : CRBoundaryTraceLog L F) :
    PhaseVelocityBoundaryTrace L F where
  gradField := fun I ρ p => (-(h.gradU I ρ p).2, 0)
  trace_eq := by
    intro I ρ t ht
    have hCR := h.phaseVel_eq_neg_dy I ρ t ht
    -- unfold and simplify
    simpa using hCR

end CRBoundaryTraceInterfaces

end Port
end RiemannRecognitionGeometry
