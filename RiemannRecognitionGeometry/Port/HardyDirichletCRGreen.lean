/-
# Port scaffold: HardyDirichlet/CRGreen → Recognition Geometry cofactor Green bound

This file mirrors the *shape* of the CR/Green pairing step from the disabled blueprint:

`/Users/jonathanwashburn/Projects/reality/IndisputableMonolith/RH/HardyDirichlet/CRGreen.lean.disabled`.

In that development, the key analytic statement is (schematically):

1. **Green pairing**:
   \[
     \int_I \varphi_I(t)\,(-W'(t))\,dt = \iint_{Q(I)} \nabla U \cdot \nabla V_I \,(\sigma-1/2)\,d\sigma\,dt
   \]

2. **Cauchy–Schwarz + window energy**:
   \[
     |\int_I \varphi_I(-W')| \le C_{\mathrm{geom}}\sqrt{E_Q(U)}\cdot |I|^{-1/2}
   \]

3. **Energy cancellation** (since `E_Q(U) ≤ E·|I|`):
   \[
     |\int_I \varphi_I(-W')| \le C_{\mathrm{geom}}\sqrt{E}
   \]

For Recognition Geometry, the “boundary phase” object is packaged modulo \(2π\) as
`rgCofactorPhaseAngle ρ t` (see `RiemannRecognitionGeometry/Phase.lean`), and the consumer needs
an inequality of the form:

`‖Δ phase‖ ≤ C_geom * sqrt(E * |I|) * (1/sqrt(|I|))`.

We record that final bound as a target interface parameterized by an abstract box-energy functional.
-/

import RiemannRecognitionGeometry.Phase

noncomputable section

namespace RiemannRecognitionGeometry
namespace Port

/-- A Hardy/Dirichlet-style CR/Green interface for bounding **cofactor phase change**
from a Carleson-box energy upper bound.

`Ebox ρ I` should be interpreted as the raw (weighted) box energy over `I` for the harmonic field
`U = Re log 𝒥_cofactor` associated to the zero `ρ`.

This is a *target interface*: we do not prove it here. It is meant to be discharged by porting
the Green identity bookkeeping (and any boundary-term gates) from the blueprint into this repo. -/
structure HardyDirichletCRGreen (Ebox : ℂ → WhitneyInterval → ℝ) : Prop where
  /-- The CR/Green phase bound, stated in the same normalized form used in
  `ClassicalAnalysisAssumptions.cofactor_green_identity_axiom_statement`. -/
  cofactor_phase_change_bound :
    ∀ (I : WhitneyInterval) (ρ : ℂ) (E : ℝ),
      0 < E →
      Ebox ρ I ≤ E * (2 * I.len) →
      ‖rgCofactorPhaseAngle ρ (I.t0 + I.len) - rgCofactorPhaseAngle ρ (I.t0 - I.len)‖ ≤
        C_geom * Real.sqrt (E * (2 * I.len)) * (1 / Real.sqrt (2 * I.len))

/-- A *strong* (more direct) CR/Green interface:
it bounds phase change in terms of the **actual box energy** `Ebox ρ I`,
rather than an auxiliary density parameter `E`.

This is the natural target of a faithful Green identity + Cauchy–Schwarz proof.
The weaker `HardyDirichletCRGreen` API is then recovered by monotonicity of `Real.sqrt`
from `Ebox ρ I ≤ E · |I|`. -/
structure HardyDirichletCRGreenStrong (Ebox : ℂ → WhitneyInterval → ℝ) : Prop where
  /-- Sanity: box energy is nonnegative. -/
  Ebox_nonneg : ∀ ρ I, 0 ≤ Ebox ρ I

  /-- Strong CR/Green bound (energy form). -/
  cofactor_phase_change_bound_strong :
    ∀ (I : WhitneyInterval) (ρ : ℂ),
      ‖rgCofactorPhaseAngle ρ (I.t0 + I.len) - rgCofactorPhaseAngle ρ (I.t0 - I.len)‖ ≤
        C_geom * Real.sqrt (Ebox ρ I) * (1 / Real.sqrt (2 * I.len))

/-- The strong energy-form CR/Green bound implies the weaker API that quantifies over
an energy density parameter `E`. -/
theorem hardyDirichletCRGreen_of_strong {Ebox : ℂ → WhitneyInterval → ℝ}
    (h : HardyDirichletCRGreenStrong Ebox) :
    HardyDirichletCRGreen Ebox := by
  refine ⟨?_⟩
  intro I ρ E hE_pos hEbox
  have hlen_pos : 0 < (2 * I.len : ℝ) := by nlinarith [I.len_pos]
  have hlen_nonneg : 0 ≤ (2 * I.len : ℝ) := le_of_lt hlen_pos
  have hE_nonneg : 0 ≤ E := le_of_lt hE_pos
  -- From `Ebox ≤ E·|I|`, we get `√Ebox ≤ √(E·|I|)`.
  have hsqrt_le : Real.sqrt (Ebox ρ I) ≤ Real.sqrt (E * (2 * I.len)) := by
    exact Real.sqrt_le_sqrt hEbox
  -- Finish by monotonicity under multiplication by nonnegative factors.
  have h0 :=
    h.cofactor_phase_change_bound_strong I ρ
  -- `C_geom` and `1/√(2*I.len)` are nonnegative.
  have hC_nonneg : 0 ≤ C_geom := by
    -- `C_geom = 1/2`.
    simp [RiemannRecognitionGeometry.C_geom]
  have hden_nonneg : 0 ≤ (1 / Real.sqrt (2 * I.len) : ℝ) :=
    one_div_nonneg.mpr (Real.sqrt_nonneg _)
  -- Replace `√Ebox` by the larger `√(E·|I|)` on the RHS.
  have : C_geom * Real.sqrt (Ebox ρ I) * (1 / Real.sqrt (2 * I.len))
            ≤ C_geom * Real.sqrt (E * (2 * I.len)) * (1 / Real.sqrt (2 * I.len)) := by
    -- Multiply the inequality `hsqrt_le` by nonneg factors.
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt_le hC_nonneg) hden_nonneg
  exact le_trans h0 this

end Port
end RiemannRecognitionGeometry
