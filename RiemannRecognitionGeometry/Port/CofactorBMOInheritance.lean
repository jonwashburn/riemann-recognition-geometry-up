/-
# Port target: BMO inheritance for the cofactor boundary data

Our Port-based “Blaschke dominates total” route currently needs a BMO certificate for the
cofactor boundary log-modulus:

`InBMOWithBound (cofactorLogAbs ρ) M`.

However, the RG main line is phrased in terms of an oscillation certificate for `logAbsXi`,
so we want an explicit bridge producing a cofactor BMO certificate from the `logAbsXi` one.

`InBMOWithBound logAbsXi M  ⟹  InBMOWithBound (cofactorLogAbs ρ) M'`.

This file packages that bridge as a target interface that we can later discharge
by porting the relevant real-analysis lemmas (e.g. log-singularity oscillation bounds).

With the current Port modeling (`cofactorLogAbs ρ = logAbsXi`), this inheritance is **definitionally trivial**.
We keep it as an explicit interface because in a more faithful model (where one works with a genuine cofactor
harmonic field rather than the Poisson extension of `logAbsXi`) it becomes a real analytic lemma.
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

/-- Trivial instance of `CofactorBMOInheritance` for the current Port model
(`cofactorLogAbs ρ` is definitionally `logAbsXi`). -/
theorem cofactorBMOInheritance_trivial : CofactorBMOInheritance := by
  refine ⟨?_⟩
  intro ρ M _hρ_re h
  simpa [cofactorLogAbs] using h

end Port
end RiemannRecognitionGeometry
