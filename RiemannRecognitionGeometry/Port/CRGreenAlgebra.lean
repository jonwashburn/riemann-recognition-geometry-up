import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section

namespace RiemannRecognitionGeometry
namespace Port

open MeasureTheory Real

section
variable {α : Type*} [MeasurableSpace α]

/-!
### Algebra: pairing + remainder ⇒ boundary bound

This file ports the **purely algebraic** core of the CR/Green step from `riemann-finish`
(`rh/RS/CRGreenOuter.lean`) into this repo.

It intentionally does **not** commit to any specific PDE/harmonic objects (`U`, `Vψ`, boundary terms, …).
Instead, it packages the two inequalities that arise after all analytic work is done:

1. a pairing bound of the form `|⟪∇U, ∇(χVψ)⟫_Q| ≤ C_pair * √E`,
2. a remainder/control bound of the form `|⟪∇U, ∇(χVψ)⟫_Q - ∫_I ψ·B| ≤ C_rem * √E`,

and shows that they imply the desired boundary integral bound
`|∫_I ψ·B| ≤ (C_pair + C_rem) * √E`.

These lemmas are the right “micro-interface” to target when replacing the current non-faithful
`ClassicalAnalysisAssumptions.*green_identity_axiom_statement` axioms with faithful energy-based proofs.
-/

/--
**Whitney pairing algebra** (ported):

If
- the volume pairing is bounded by `C_pair * √E`, and
- the difference between volume pairing and boundary integral is bounded by `C_rem * √E`,

then the boundary integral is bounded by `(C_pair + C_rem) * √E`.
-/
theorem pairing_whitney_analytic_bound
    {μ : Measure α} {Q : Set α} {I : Set ℝ}
    (pairing : α → ℝ) (ψ B : ℝ → ℝ)
    (E : ℝ) (C_pair C_rem : ℝ)
    (hPair : |∫ x in Q, pairing x ∂μ| ≤ C_pair * Real.sqrt E)
    (hRem :
      |(∫ x in Q, pairing x ∂μ) - (∫ t in I, ψ t * B t ∂volume)| ≤ C_rem * Real.sqrt E) :
    |∫ t in I, ψ t * B t ∂volume| ≤ (C_pair + C_rem) * Real.sqrt E := by
  classical
  set LHS : ℝ := ∫ x in Q, pairing x ∂μ
  set BD : ℝ := ∫ t in I, ψ t * B t ∂volume
  -- `|BD| ≤ |LHS| + |LHS-BD|`
  have htri : |BD| ≤ |LHS| + |LHS - BD| := by
    have hsum : LHS + (BD - LHS) = BD := by
      -- `LHS + BD - LHS = BD`
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (add_sub_cancel LHS BD)
    have h0 : |LHS + (BD - LHS)| ≤ |LHS| + |BD - LHS| :=
      abs_add LHS (BD - LHS)
    have : |BD| ≤ |LHS| + |BD - LHS| := by
      simpa [hsum] using h0
    simpa [abs_sub_comm] using this
  have hsum : |LHS| + |LHS - BD| ≤ (C_pair + C_rem) * Real.sqrt E := by
    have h1 : |LHS| ≤ C_pair * Real.sqrt E := by simpa [LHS] using hPair
    have h2 : |LHS - BD| ≤ C_rem * Real.sqrt E := by
      simpa [LHS, BD] using hRem
    have : |LHS| + |LHS - BD| ≤ C_pair * Real.sqrt E + C_rem * Real.sqrt E :=
      add_le_add h1 h2
    have hfactor :
        C_pair * Real.sqrt E + C_rem * Real.sqrt E = (C_pair + C_rem) * Real.sqrt E := by
      simpa [add_mul] using (add_mul C_pair C_rem (Real.sqrt E)).symm
    exact le_trans this (le_of_eq hfactor)
  exact le_trans htri hsum

end

end Port
end RiemannRecognitionGeometry
