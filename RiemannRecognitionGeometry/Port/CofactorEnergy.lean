/-
# Port step: a concrete candidate for the RG “cofactor box energy” functional

In `REALITY_PORT_PLAN.md` we decided to port the Hardy/Dirichlet pipeline in a statement-driven way.
To even state that path cleanly, we need a concrete “energy functional” `Ebox ρ I` that represents
the Carleson-box (Dirichlet) energy of the RG **cofactor** harmonic field.

**Important modeling choice**:
in the half-plane factorization relevant to RG, the “Blaschke factor” attached to an off-line zero
is an **inner function** with modulus 1 on the boundary line `Re s = 1/2`. Consequently the boundary
log-modulus of the cofactor agrees with `logAbsXi` (there is no “subtract log|s-ρ|” term on the boundary).

So in this Port layer we model the cofactor boundary log-modulus as just `logAbsXi` (but we keep the
parameter `ρ` in the signature to match the Hardy/Dirichlet interfaces).
-/

import RiemannRecognitionGeometry.FeffermanStein
import RiemannRecognitionGeometry.CarlesonBound
import RiemannRecognitionGeometry.PoissonExtension

noncomputable section

namespace RiemannRecognitionGeometry
namespace Port

open Real Complex

/-- Boundary log-modulus for the half-plane **inner-factor cofactor**.

Since the associated Blaschke factor has modulus 1 on the boundary line `Re s = 1/2`,
the boundary log-modulus of the cofactor is exactly `logAbsXi`.

We keep the `ρ` parameter only to match the Hardy/Dirichlet interface shapes. -/
def cofactorLogAbs (_ρ : ℂ) (t : ℝ) : ℝ :=
  logAbsXi t

/-- Gradient field of the (conjugate) Poisson extension of `cofactorLogAbs ρ`.

This uses the existing `poissonExtension_gradient` infrastructure in `FeffermanStein.lean`.
The intended interpretation is `∇U`, where `U` is the harmonic extension of the boundary data. -/
def cofactorGradField (ρ : ℂ) : (ℝ × ℝ) → (ℝ × ℝ) :=
  fun p => poissonExtension_gradient (cofactorLogAbs ρ) p.1 p.2

/-- **Candidate cofactor box energy** functional:
the Carleson-box energy of the Poisson extension of `cofactorLogAbs ρ` over `Q(I)`. -/
def cofactorEbox (ρ : ℂ) (I : WhitneyInterval) : ℝ :=
  boxEnergy (cofactorGradField ρ) I

/-- Alternative candidate energy functional, using `PoissonExtension.carleson_energy`.

This is useful when discharging energy bounds via the explicit Fefferman–Stein axiom
`PoissonExtension.bmo_carleson_embedding` (which is stated for `carleson_energy`). -/
def cofactorEbox_poisson (ρ : ℂ) (I : WhitneyInterval) : ℝ :=
  PoissonExtension.carleson_energy (cofactorLogAbs ρ) (I.t0 - I.len) (I.t0 + I.len)

end Port
end RiemannRecognitionGeometry
