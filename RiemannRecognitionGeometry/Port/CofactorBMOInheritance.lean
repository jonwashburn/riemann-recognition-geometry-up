/-!
# Port target: BMO inheritance for the Weierstrass cofactor boundary data

Our Port-based “Blaschke dominates total” route currently needs a BMO certificate for the
cofactor boundary log-modulus:

`InBMOWithBound (cofactorLogAbs ρ) M`.

However, the RG main line is phrased in terms of an oscillation certificate for `logAbsXi`.
So we need an explicit *inheritance* bridge:

`InBMOWithBound logAbsXi M  ⟹  InBMOWithBound (cofactorLogAbs ρ) M'`.

This file packages that bridge as a target interface that we can later discharge
by porting the relevant real-analysis lemmas (e.g. log-singularity oscillation bounds).

For now we keep the statement simple by asking for the **same bound** `M`.
This is slightly stronger than what is classically true (one typically gets `M + O(1)`),
but it is the cleanest interface for wiring the Port route into the existing RG numeric closure.
-/

import RiemannRecognitionGeometry.Port.CofactorEnergy

noncomputable section

namespace RiemannRecognitionGeometry
namespace Port

/-- **Target interface**: BMO inheritance for the cofactor boundary log-modulus.

When `ρ` is off the critical line (`1/2 < ρ.re`), the log-distance term is non-singular on the
critical line and one expects `cofactorLogAbs ρ` to inherit BMO from `logAbsXi`. -/
structure CofactorBMOInheritance : Prop where
  cofactor_bmo_of_logAbsXi_bmo :
    ∀ (ρ : ℂ) (M : ℝ),
      (1 / 2) < ρ.re →
      InBMOWithBound logAbsXi M →
      InBMOWithBound (cofactorLogAbs ρ) M

end Port
end RiemannRecognitionGeometry
