/-!
# Port step: discharge the Carleson budget for `cofactorEbox_poisson` from the FS axiom

This file instantiates the *budget* interface
`Port.HardyDirichletCarlesonBudget` for the concrete energy functional:

`Ebox := Port.cofactorEbox_poisson`.

The only analytic input used is the existing axiom:
`PoissonExtension.bmo_carleson_embedding`.

So after this step, the remaining work for the Carleson side is reduced to:

- proving (or assuming) `InBMOWithBound (cofactorLogAbs ρ) M` for the relevant `ρ, M`.
-/

import RiemannRecognitionGeometry.Port.HardyDirichletCarleson
import RiemannRecognitionGeometry.Port.CofactorEnergy

noncomputable section

namespace RiemannRecognitionGeometry
namespace Port

open Real Complex Set MeasureTheory

/-! ## Helpers: BMO hypothesis shape + nonnegativity of energy -/

/-- The BMO condition required by `PoissonExtension.bmo_carleson_embedding` follows directly from
our scale-correct `InBMOWithBound` certificate (because `meanOscillation` is definitionally the same
expression when `a < b`). -/
lemma poissonExtension_bmoHyp_of_InBMOWithBound {w : ℝ → ℝ} {M : ℝ} (h : InBMOWithBound w M) :
    ∀ a b : ℝ, a < b →
      (b - a)⁻¹ * ∫ t in Icc a b, |w t - (b - a)⁻¹ * ∫ s in Icc a b, w s| ≤ M := by
  intro a b hab
  -- Unfold `meanOscillation`/`intervalAverage` at `hab : a < b`.
  -- This is exactly the term in the PoissonExtension axiom.
  simpa [meanOscillation, intervalAverage, hab, one_div] using (h.2 a b hab)

/-- Nonnegativity of `PoissonExtension.carleson_energy` (it is an integral of a nonnegative density). -/
lemma poissonExtension_carleson_energy_nonneg (w : ℝ → ℝ) (a b : ℝ) :
    0 ≤ PoissonExtension.carleson_energy w a b := by
  -- Expand the nested set integrals.
  unfold PoissonExtension.carleson_energy
  -- Outer integral nonneg, since the integrand (inner integral) is nonneg for every `x`.
  refine MeasureTheory.integral_nonneg_of_ae ?_
  refine Filter.eventually_of_forall ?_
  intro x
  -- Inner integral nonneg on `Icc 0 (b-a)`.
  refine MeasureTheory.integral_nonneg_of_ae ?_
  -- On the restricted measure, membership in the set holds a.e.
  have hy_mem :
      (∀ᵐ y ∂(volume.restrict (Icc (0 : ℝ) (b - a))), y ∈ Icc (0 : ℝ) (b - a)) := by
    simpa using (MeasureTheory.ae_restrict_mem (μ := volume) (s := Icc (0 : ℝ) (b - a)))
  filter_upwards [hy_mem] with y hy
  have hy0 : 0 ≤ y := hy.1
  -- Density: y * ‖∇Q[w]‖^2 ≥ 0 when y ≥ 0.
  exact mul_nonneg hy0 (sq_nonneg _)

/-! ## Main: budget instance for `cofactorEbox_poisson` -/

/-- The Hardy/Dirichlet-style Carleson budget holds for `Ebox := cofactorEbox_poisson`,
assuming only the Fefferman–Stein BMO→Carleson embedding axiom already present in this repo. -/
theorem hardyDirichletCarlesonBudget_cofactorEbox_poisson :
    HardyDirichletCarlesonBudget cofactorEbox_poisson := by
  refine ⟨?_, ?_⟩
  · intro ρ I
    -- energy ≥ 0
    simpa [cofactorEbox_poisson] using
      poissonExtension_carleson_energy_nonneg (w := cofactorLogAbs ρ) (a := I.t0 - I.len) (b := I.t0 + I.len)
  · intro I ρ M h_bmo _hρ_zero _hρ_im
    -- Apply the Fefferman–Stein axiom on the interval endpoints.
    have h_bmo' :
        ∀ a' b' : ℝ, a' < b' →
          (b' - a')⁻¹ * ∫ t in Icc a' b', |cofactorLogAbs ρ t - (b' - a')⁻¹ * ∫ s in Icc a' b', cofactorLogAbs ρ s| ≤ M :=
      poissonExtension_bmoHyp_of_InBMOWithBound (w := cofactorLogAbs ρ) h_bmo
    have h_embed :=
      PoissonExtension.bmo_carleson_embedding
        (w := cofactorLogAbs ρ)
        (a := I.t0 - I.len) (b := I.t0 + I.len)
        (M := M) h_bmo.1 h_bmo'
    -- Rewrite the RHS into `K_tail M * (2*I.len)`.
    -- Note: (b - a) = (t0+len) - (t0-len) = 2*len.
    have h_ba : (I.t0 + I.len) - (I.t0 - I.len) = 2 * I.len := by ring
    -- Finish.
    simpa [cofactorEbox_poisson, K_tail, h_ba] using h_embed

end Port
end RiemannRecognitionGeometry
