/-
# Bundled assumptions for the B2′ (renormalized tail) driver

`Assumptions.lean` packages the original (global-BMO) oscillation target as `OscillationTarget`.
For the corrected B2′ story we keep a **separate** lightweight bundling layer to avoid import cycles:

- `OscillationTargetTail` lives in `OscillationTargetTail.lean` (and depends on local-BMO predicates).
- This file packages that hypothesis into a single structure, mirroring `OscillationAssumptions`.

It also provides an optional Route‑A bundle for the μ‑Carleson packing hypothesis.
-/

import RiemannRecognitionGeometry.MuCarlesonToTailDecay
import RiemannRecognitionGeometry.MuCarlesonOps

noncomputable section

namespace RiemannRecognitionGeometry

/-- Bundled B2′ hypothesis (Lean-facing). -/
structure OscillationTailAssumptions : Prop where
  oscillationTargetTail : OscillationTargetTail

/-- Bundled Route‑A hypothesis: μ-Carleson packing for the (opaque) off-critical zero measure. -/
structure MuCarlesonAssumptions : Prop where
  muCarleson :
    ∃ (Cμ : ENNReal) (α : ℝ), MuCarleson muOffCritical Cμ α

/-- Bundled Route‑A hypothesis (refined): split μ into a measurable “near” region `S` and its complement.

This is designed to reflect what the recent literature supports:
- many explicit/modern results control **far-right** zeros (a natural candidate for `Sᶜ`),
- while the near-critical regime remains the hard part.

Formally: if both restricted measures are μ-Carleson, then μ is μ-Carleson by
`MuCarleson.of_restrict_compl` (see `MuCarlesonOps.lean`). -/
structure MuCarlesonSplitAssumptions : Prop where
  /-- Existential packaging to keep this bundle a `Prop` (no data fields).

  Interprets as: there exists a measurable set `S` and Carleson constants `Cnear`, `Cfar`
  such that μ restricted to `S` and to `Sᶜ` are both μ‑Carleson (with aperture 2). -/
  split :
    ∃ (S : Set (ℝ × ℝ)) (Cnear Cfar : ENNReal),
      MeasurableSet S ∧
      MuCarleson (muOffCritical.restrict S) Cnear 2 ∧
      MuCarleson (muOffCritical.restrict Sᶜ) Cfar 2

namespace MuCarlesonSplitAssumptions

theorem muCarleson (h : MuCarlesonSplitAssumptions) :
    ∃ Cμ : ENNReal, MuCarleson muOffCritical Cμ 2 := by
  rcases h.split with ⟨S, Cnear, Cfar, hS, hNear, hFar⟩
  refine ⟨Cnear + Cfar, ?_⟩
  exact MuCarleson.of_restrict_compl (μ := muOffCritical) (α := 2) hS hNear hFar

theorem oscillationTargetTail (h : MuCarlesonSplitAssumptions) : OscillationTargetTail := by
  -- convert split Carleson into a single Carleson hypothesis, then use the existing Route‑A stub
  rcases h.split with ⟨S, Cnear, Cfar, hS, hNear, hFar⟩
  have hμ : MuCarleson muOffCritical (Cnear + Cfar) 2 :=
    MuCarleson.of_restrict_compl (μ := muOffCritical) (α := 2) hS hNear hFar
  exact oscillationTargetTail_of_muCarleson_via_decay (Cμ := Cnear + Cfar) (α := 2) hμ

end MuCarlesonSplitAssumptions

namespace MuCarlesonAssumptions

/-- Route‑A ⇒ B2′ (stubbed): μ‑Carleson implies the B2′ oscillation target. -/
theorem oscillationTargetTail (h : MuCarlesonAssumptions) : OscillationTargetTail :=
  by
    rcases h.muCarleson with ⟨Cμ, α, hμ⟩
    exact oscillationTargetTail_of_muCarleson_via_decay (Cμ := Cμ) (α := α) hμ

end MuCarlesonAssumptions

end RiemannRecognitionGeometry
