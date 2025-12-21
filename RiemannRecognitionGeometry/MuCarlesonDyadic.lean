/-
# μ-Carleson bookkeeping on dyadic Carleson boxes/annuli (Route A scaffold)

This file provides the measure-theoretic “bookkeeping lemmas” used in the Route‑A proof skeleton:
from a μ‑Carleson hypothesis, bound the μ-mass of the dyadic boxes `Qbox I j` and annuli `Abox I j`.

These lemmas are purely structural (no number theory); they let the plan’s annulus decomposition
be expressed cleanly in Lean.
-/

import RiemannRecognitionGeometry.MuCarleson
import RiemannRecognitionGeometry.DyadicCarlesonAnnuli

noncomputable section

namespace RiemannRecognitionGeometry

open Real MeasureTheory Set

/-! ## Basic bounds from μ-Carleson -/

lemma mu_Qbox_le_of_MuCarleson
    {μ : Measure (ℝ × ℝ)} {Cμ : ENNReal}
    (hμ : MuCarleson μ Cμ 2) (I : WhitneyInterval) (j : ℕ) :
    μ (Qbox I j) ≤ Cμ * ENNReal.ofReal (2 * (dyadicDilate I j).len) := by
  -- `Qbox I j = carlesonBox (dyadicDilate I j) 2`
  simpa [Qbox] using (hμ (dyadicDilate I j))

lemma mu_Abox_le_of_MuCarleson
    {μ : Measure (ℝ × ℝ)} {Cμ : ENNReal}
    (hμ : MuCarleson μ Cμ 2) (I : WhitneyInterval) (j : ℕ) :
    μ (Abox I j) ≤ Cμ * ENNReal.ofReal (2 * (dyadicDilate I (j+1)).len) := by
  have hsub : Abox I j ⊆ Qbox I (j+1) := Abox_subset_Qbox_succ I j
  have : μ (Abox I j) ≤ μ (Qbox I (j+1)) := measure_mono hsub
  have hQ := mu_Qbox_le_of_MuCarleson (hμ := hμ) (I := I) (j := j+1)
  exact le_trans this hQ

end RiemannRecognitionGeometry
