import RiemannRecognitionGeometry.Port.CofactorCRGreenS2Interfaces
import RiemannRecognitionGeometry.Port.CRBoundaryTraceInterfaces

noncomputable section

namespace RiemannRecognitionGeometry
namespace Port

open Real Complex

namespace CofactorOuterLogBranch

open CofactorCRGreenS2Interfaces
open CRBoundaryTraceInterfaces

/-!
## Holistic cofactor “outer/log-branch” package (Port interface)

The current RG/Port CR–Green bottleneck has been shrunk to a very small but crucial analytic gate:

`PhaseVelocityBoundaryTracePoissonPairing` in
`Port/CofactorCRGreenS2Interfaces.lean`.

This file introduces a **single “holistic” interface** intended to capture the classical content
behind that gate:

- there is a *faithful* real-valued phase lift `θ` of the cofactor phase on Whitney bases,
- `θ` admits an FTC-valid phase velocity `θ'`,
- and `θ'` is tied to the **same Poisson-model field** used in the Carleson/Dirichlet energy
  `cofactorEbox_poisson` via the minimal pairing/distributional convergence.

We do **not** prove any of the analytic boundary theory here; this is statement-shape only.
The point is to stop treating the Poisson pairing/trace as an orphan gate and instead make it the
output of one named “outer/log-branch” package that matches how the written proof should read.
-/

/--
`CofactorOuterLogBranch` is the Port-level “one object to rule them all” for the cofactor CR/Green
boundary-term bookkeeping.

It is deliberately minimal: it packages exactly the three sub-ingredients that the CR/Green algebra
actually consumes (lift + FTC + Poisson pairing).

In a faithful analytic proof, this would be discharged from an actual holomorphic, nonvanishing
cofactor `F` on a half-plane with a holomorphic logarithm branch `Log F = u + i v`, where:
- `u` has boundary values `cofactorLogAbs ρ` (here modeled as `logAbsXi`), and
- `v` provides the phase lift `θ`, with `θ'` identified as the appropriate Poisson/CR boundary trace.
-/
structure CofactorOuterLogBranch where
  /-- A real-valued phase lift on Whitney bases. -/
  L : CofactorPhaseLift
  /-- An FTC-valid phase velocity for the lift. -/
  F : PhaseVelocityFTC L
  /-- Minimal non-vacuous link to the Poisson-model field (pairing/distributional strength). -/
  poissonPairing : PhaseVelocityBoundaryTracePoissonPairing L F

/-- Convenience: the holistic package immediately yields the bundled Green-trace gate. -/
def greenTraceIdentity (h : CofactorOuterLogBranch) : GreenTraceIdentity :=
  GreenTraceIdentity.of_lift_and_ftc h.L h.F

/-- Convenience: expose the lift gate as a standalone object. -/
def phaseLift (h : CofactorOuterLogBranch) : CofactorPhaseLift := h.L

/-- Convenience: expose the FTC gate as a standalone object. -/
def phaseVelocityFTC (h : CofactorOuterLogBranch) : PhaseVelocityFTC h.L := h.F

/-- Convenience: expose the Poisson pairing gate (the current boxed wall). -/
def phaseVelocityBoundaryTracePoissonPairing (h : CofactorOuterLogBranch) :
    PhaseVelocityBoundaryTracePoissonPairing h.L h.F :=
  h.poissonPairing

/--
Optional wiring: if one additionally provides a CR boundary-trace identity (log-branch style),
then one can recover the weaker Port boundary-trace hook.

This is not part of the holistic package itself (since our boxed target is Poisson pairing),
but it is often a semantic stepping-stone in the written proof.
-/
def phaseVelocityBoundaryTrace_of_CR
    (h : CofactorOuterLogBranch)
    (hCR : CRBoundaryTraceLog h.L h.F) :
    PhaseVelocityBoundaryTrace h.L h.F :=
  phaseVelocityBoundaryTrace_of_CRBoundaryTraceLog hCR

end CofactorOuterLogBranch

end Port
end RiemannRecognitionGeometry
