/-
# Annulus tail scaffold (Route‑A, Step 2.4 → Step 5)

This file implements the *purely geometric / summation* closure step in the B2′ Route‑A plan:

If a family of nonnegative “annulus contributions” `T j` (for `j > K`) satisfies a geometric decay

`T j ≤ c * (1/2)^j`,

then the total tail contribution is bounded by `c * (1/2)^K`.

All number-theory/analysis content (μ‑Carleson, single-zero influence, annulus decay, etc.) is
deliberately *not* proved here; this module is only the constant‑chase / geometric‑series wrapper.
-/

import RiemannRecognitionGeometry.GeometricTail
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Instances.ENNReal.Lemmas

noncomputable section

namespace RiemannRecognitionGeometry

open Real

/-- Generic “tail sum” operator for annulus-indexed contributions starting after a cutoff `K`. -/
def annulusTailSum (K : ℕ) (T : ℕ → ℝ) : ℝ :=
  ∑' (j : ℕ), (if j > K then T j else 0)

/-- **Geometric tail closure**: if each annulus contribution decays like `c*(1/2)^j` for `j > K`,
then the whole tail is `≤ c*(1/2)^K`. -/
theorem annulusTailSum_le_geometric (K : ℕ) {c : ℝ} (hc : 0 ≤ c) {T : ℕ → ℝ}
    (hT_nonneg : ∀ j, j > K → 0 ≤ T j)
    (hT : ∀ j, j > K → T j ≤ c * (1/2 : ℝ)^j) :
    annulusTailSum K T ≤ c * (1/2 : ℝ)^K := by
  -- Compare termwise to the geometric majorant, then apply the already-proved geometric tail bound.
  let f : ℕ → ℝ := fun j => if j > K then T j else 0
  let g : ℕ → ℝ := fun j => if j > K then c * (1/2 : ℝ)^j else 0

  have hf_nonneg : ∀ j, 0 ≤ f j := by
    intro j
    by_cases hj : j > K
    · simpa [f, hj] using hT_nonneg j hj
    · simp [f, hj]

  have hg_nonneg : ∀ j, 0 ≤ g j := by
    intro j
    by_cases hj : j > K
    · have : 0 ≤ c * (1/2 : ℝ)^j := by
        exact mul_nonneg hc (pow_nonneg (by norm_num : (0 : ℝ) ≤ (1/2 : ℝ)) _)
      simpa [g, hj] using this
    · simp [g, hj]

  have hfg : ∀ j, f j ≤ g j := by
    intro j
    by_cases hj : j > K
    · simpa [f, g, hj] using hT j hj
    · simp [f, g, hj]

  -- Summability of the geometric majorant.
  have hgeom : Summable (fun j : ℕ => (1/2 : ℝ)^j) := by
    -- `1/2` is `((1 : ℝ) / 2)`; use the standard geometric-series lemma.
    simpa [one_div] using (summable_geometric_two : Summable fun j : ℕ ↦ ((1 : ℝ) / 2) ^ j)

  have hgeom_mul : Summable (fun j : ℕ => c * (1/2 : ℝ)^j) :=
    Summable.mul_left c hgeom

  have hg_summable : Summable g := by
    -- `g` is an indicator/truncation of a summable series.
    refine Summable.of_nonneg_of_le (f := fun j : ℕ => c * (1/2 : ℝ)^j) (g := g) hg_nonneg ?_ hgeom_mul
    intro j
    by_cases hj : j > K
    · simp [g, hj]
    · -- outside the tail, `g j = 0 ≤ c*(1/2)^j`
      have : 0 ≤ c * (1/2 : ℝ)^j :=
        mul_nonneg hc (pow_nonneg (by norm_num : (0 : ℝ) ≤ (1/2 : ℝ)) _)
      simpa [g, hj] using this

  have hf_summable : Summable f :=
    Summable.of_nonneg_of_le (f := g) (g := f) hf_nonneg hfg hg_summable

  have hsum : (∑' j, f j) ≤ ∑' j, g j :=
    tsum_le_tsum hfg hf_summable hg_summable

  -- Finish with the geometric tail lemma from `GeometricTail.lean`.
  have hgeo := far_field_geometric_bound_mul K (c := c) hc
  -- Unfold `annulusTailSum` and chain inequalities.
  dsimp [annulusTailSum, f, g]
  exact le_trans hsum hgeo

end RiemannRecognitionGeometry
