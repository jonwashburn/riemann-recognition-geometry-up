/-!
# Port step: a concrete candidate for the RG “cofactor box energy” functional

In `REALITY_PORT_PLAN.md` we decided to try the **Fefferman–Stein + BMO inheritance** route first.
To even state that path cleanly, we need a concrete “energy functional” `Ebox ρ I` that represents
the Carleson-box (Dirichlet) energy of the RG cofactor harmonic field.

This file defines one natural candidate in terms of existing primitives in this repo:

- boundary function: `cofactorLogAbs ρ t = log|ξ(1/2+it)| - log|((1/2+it) - ρ)|`,
- harmonic extension: Poisson extension of that boundary function (already modeled in `FeffermanStein.lean`),
- energy: Carleson-box energy of its gradient over the Whitney box `Q(I)` (already modeled in `CarlesonBound.lean`).

This is *not yet* the full “Re log 𝒥” field from the Hardy/Dirichlet product certificate story, but it is a
reasonable concrete target for the RG cofactor energy budget interface.
-/

import RiemannRecognitionGeometry.FeffermanStein
import RiemannRecognitionGeometry.CarlesonBound
import RiemannRecognitionGeometry.PoissonExtension

noncomputable section

namespace RiemannRecognitionGeometry
namespace Port

open Real Complex

/-- Boundary log-modulus for the Weierstrass cofactor `g(s) = ξ(s)/(s-ρ)` on the critical line.

This is the obvious “subtract the log singularity” model:
`log|g(1/2+it)| = log|ξ(1/2+it)| - log|((1/2+it)-ρ)|`.

We reuse the existing regularized `logAbsXi` for `log|ξ|` (see `FeffermanStein.lean`). -/
def cofactorLogAbs (ρ : ℂ) (t : ℝ) : ℝ :=
  logAbsXi t - Real.log (Complex.abs (((1/2 : ℂ) + t * Complex.I) - ρ))

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
