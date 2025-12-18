/-
# Port step: Carleson budget instance for the xi energy functional

We already have the Hardy/Dirichlet Carleson budget instance for
`Ebox := cofactorEbox_poisson`.

For symmetry (and to match the blueprint decomposition), we also provide the same budget instance
for the *xi* energy functional:

`Ebox_xi ρ I := xiEbox_poisson I`.

This is immediate from the existing Fefferman–Stein axiom
`PoissonExtension.bmo_carleson_embedding`, and uses the same helper lemmas as the cofactor budget.
-/

import RiemannRecognitionGeometry.Port.HardyDirichletCarleson
import RiemannRecognitionGeometry.Port.XiEnergy
import RiemannRecognitionGeometry.Port.CofactorCarlesonBudget

noncomputable section

namespace RiemannRecognitionGeometry
namespace Port

open Real Complex Set MeasureTheory

/-- `xiEbox_poisson` packaged as a Hardy/Dirichlet `Ebox` functional. -/
def xiEbox_poissonEbox (_ρ : ℂ) (I : WhitneyInterval) : ℝ :=
  xiEbox_poisson I

/-- The Hardy/Dirichlet Carleson budget holds for `Ebox := xiEbox_poissonEbox`,
using only the existing Fefferman–Stein axiom in `PoissonExtension`. -/
theorem hardyDirichletCarlesonBudget_xiEbox_poisson :
    HardyDirichletCarlesonBudget xiEbox_poissonEbox := by
  refine ⟨?_, ?_⟩
  · intro ρ I
    -- energy ≥ 0
    -- (This is the same nonnegativity lemma used for `cofactorEbox_poisson`.)
    simpa [xiEbox_poissonEbox, xiEbox_poisson] using
      poissonExtension_carleson_energy_nonneg (w := logAbsXi) (a := I.t0 - I.len) (b := I.t0 + I.len)
  · intro I ρ M h_bmo _hρ_zero _hρ_im
    -- In the current Port model, `cofactorLogAbs ρ = logAbsXi`, so `h_bmo` is exactly a BMO bound for `logAbsXi`.
    have h_osc : InBMOWithBound logAbsXi M := by
      simpa [cofactorLogAbs] using h_bmo
    -- Apply the Fefferman–Stein axiom on the interval endpoints.
    have h_bmo' :
        ∀ a' b' : ℝ, a' < b' →
          (b' - a')⁻¹ * ∫ t in Icc a' b', |logAbsXi t - (b' - a')⁻¹ * ∫ s in Icc a' b', logAbsXi s| ≤ M :=
      poissonExtension_bmoHyp_of_InBMOWithBound (w := logAbsXi) h_osc
    have h_embed :=
      PoissonExtension.bmo_carleson_embedding
        (w := logAbsXi)
        (a := I.t0 - I.len) (b := I.t0 + I.len)
        (M := M) h_osc.1 h_bmo'
    have h_ba : (I.t0 + I.len) - (I.t0 - I.len) = 2 * I.len := by ring
    -- Finish.
    simpa [xiEbox_poissonEbox, xiEbox_poisson, K_tail, h_ba] using h_embed

end Port
end RiemannRecognitionGeometry
