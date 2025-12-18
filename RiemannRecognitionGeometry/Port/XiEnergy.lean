/-
# Port step: explicit “xi box energy” functional for the upper bound route

The RG contradiction uses an **upper bound** on the total phase signal
`totalPhaseSignal I = xiPhaseChange I`.

To make the CR/Green step *energy-based* (instead of the older non-faithful
`ClassicalAnalysisAssumptions.green_identity_axiom_statement`), we introduce an explicit
energy functional for the boundary datum `logAbsXi`.

We deliberately reuse the same “PoissonExtension carleson_energy” functional already used in the
Port Carleson-budget route (`cofactorEbox_poisson`), so we can keep using the existing
Fefferman–Stein axiom `PoissonExtension.bmo_carleson_embedding`.
-/

import RiemannRecognitionGeometry.Port.CofactorEnergy

noncomputable section

namespace RiemannRecognitionGeometry
namespace Port

open Real

/-- Energy functional over the Whitney box `Q(I)` for the boundary datum `logAbsXi`. -/
def xiEbox_poisson (I : WhitneyInterval) : ℝ :=
  PoissonExtension.carleson_energy logAbsXi (I.t0 - I.len) (I.t0 + I.len)

@[simp] lemma cofactorEbox_poisson_eq_xiEbox_poisson (ρ : ℂ) (I : WhitneyInterval) :
    cofactorEbox_poisson ρ I = xiEbox_poisson I := by
  -- `cofactorLogAbs ρ` is definitionally `logAbsXi` (up to η-expansion).
  have hw : cofactorLogAbs ρ = logAbsXi := by
    funext t
    simp [cofactorLogAbs]
  simp [cofactorEbox_poisson, xiEbox_poisson, hw]

end Port
end RiemannRecognitionGeometry
