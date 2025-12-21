/-
# B2′ constant-chase scaffold

This file packages the purely formal “pick K large enough” step that appears in the B2′ plan.

Given any decay estimate of the form

`meanOscillation (tailLogAbs I ρ K) x y ≤ c * (1/2)^K`

uniformly over all relevant subintervals `[x,y] ⊆ I_R`, we can choose a single cutoff `K`
so that `c*(1/2)^K ≤ C_tail`, and thus obtain `OscillationTargetTail`.

This isolates the deep math into proving such a decay estimate (typically via μ‑Carleson +
annulus decay + energy → BMO), while keeping the engineering step executable in Lean.
-/

import RiemannRecognitionGeometry.OscillationTargetTail
import RiemannRecognitionGeometry.GeometricTail

noncomputable section

namespace RiemannRecognitionGeometry

open Real Complex

/-- A convenient “decay hypothesis” shape for B2′: at cutoff `K`, the renormalized tail datum
has mean oscillation on `I_R` bounded by `c*(1/2)^K`. -/
def TailMeanOscDecay (c : ℝ) : Prop :=
  ∀ (K : ℕ) (ρ : ℂ) (I : WhitneyInterval) (x y : ℝ),
    (I.t0 - I.len) ≤ x → y ≤ (I.t0 + I.len) → x < y →
    meanOscillation (fun t => tailLogAbs I ρ K t) x y ≤ c * (1/2 : ℝ)^K

/-- **Constant chase**: a decay hypothesis implies `OscillationTargetTail` by choosing `K` so that
`c*(1/2)^K ≤ C_tail`. -/
theorem oscillationTargetTail_of_decay {c : ℝ} (hc : 0 ≤ c) (hdec : TailMeanOscDecay c) :
    OscillationTargetTail := by
  have hCtail : 0 < C_tail := by
    unfold C_tail
    norm_num
  rcases exists_pow_half_mul_le (ε := C_tail) (c := c) hCtail hc with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro ρ I
  refine ⟨hCtail, ?_⟩
  intro x y hx hy hxy
  have hmo : meanOscillation (fun t => tailLogAbs I ρ K t) x y ≤ c * (1/2 : ℝ)^K :=
    hdec K ρ I x y hx hy hxy
  exact le_trans hmo hK

end RiemannRecognitionGeometry
