/-
# μ-Carleson operations (restriction, sum, and splitting)

This file adds small, reusable measure-theoretic lemmas about the Lean-facing predicate

`MuCarleson μ Cμ α := ∀ I, μ (carlesonBox I α) ≤ Cμ * |I|`.

These are used to:
- split μ into “near” and “far” regimes (restriction to a measurable set and its complement),
- recombine Carleson bounds additively,
- and thread “literature-only controls the far regime” through the assumption bundles.
-/

import RiemannRecognitionGeometry.MuCarleson
import RiemannRecognitionGeometry.DyadicCarlesonAnnuliMeasure

noncomputable section

namespace RiemannRecognitionGeometry

open Real MeasureTheory Set

/-! ## Basic closure properties -/

/-! ## Standard “near/far” split sets -/

/-- The canonical “near” region for a σ-split: points with `σ ≤ δ`.

We store points as `(t,σ)` in `ℝ×ℝ`, so this is `{p | p.2 ≤ δ}`. -/
def sigmaLeSet (δ : ℝ) : Set (ℝ × ℝ) := { p : ℝ × ℝ | p.2 ≤ δ }

lemma measurableSet_sigmaLeSet (δ : ℝ) : MeasurableSet (sigmaLeSet δ) := by
  -- measurability of `{p | p.2 ≤ δ}` follows from measurability of the second projection
  simpa [sigmaLeSet] using (measurableSet_le measurable_snd measurable_const)

/-- Restricting a μ-Carleson measure to a measurable subset preserves the same Carleson constant. -/
lemma MuCarleson.restrict
    {μ : Measure (ℝ × ℝ)} {Cμ : ENNReal} {α : ℝ}
    (hμ : MuCarleson μ Cμ α) {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) :
    MuCarleson (μ.restrict S) Cμ α := by
  intro I
  have hsub : carlesonBox I α ∩ S ⊆ carlesonBox I α := by
    intro p hp; exact hp.1
  -- `μ.restrict S (Q) = μ(Q ∩ S) ≤ μ(Q)`
  have hle : (μ.restrict S) (carlesonBox I α) ≤ μ (carlesonBox I α) := by
    rw [Measure.restrict_apply' hS]
    exact measure_mono hsub
  exact le_trans hle (hμ I)

/-- The sum of two μ-Carleson measures is μ-Carleson with constant `C₁ + C₂`. -/
lemma MuCarleson.add
    {μ₁ μ₂ : Measure (ℝ × ℝ)} {C₁ C₂ : ENNReal} {α : ℝ}
    (h₁ : MuCarleson μ₁ C₁ α) (h₂ : MuCarleson μ₂ C₂ α) :
    MuCarleson (μ₁ + μ₂) (C₁ + C₂) α := by
  intro I
  have h1 := h₁ I
  have h2 := h₂ I
  -- unfold the measure addition on the box
  have hadd : (μ₁ + μ₂) (carlesonBox I α) =
      μ₁ (carlesonBox I α) + μ₂ (carlesonBox I α) := by
    simp
  -- add the two bounds and fold constants
  have hsum :
      μ₁ (carlesonBox I α) + μ₂ (carlesonBox I α)
        ≤ C₁ * ENNReal.ofReal (2 * I.len) + C₂ * ENNReal.ofReal (2 * I.len) := by
    exact add_le_add h1 h2
  calc
    (μ₁ + μ₂) (carlesonBox I α)
        = μ₁ (carlesonBox I α) + μ₂ (carlesonBox I α) := hadd
    _ ≤ C₁ * ENNReal.ofReal (2 * I.len) + C₂ * ENNReal.ofReal (2 * I.len) := hsum
    _ = (C₁ + C₂) * ENNReal.ofReal (2 * I.len) := by
          simpa using (add_mul C₁ C₂ (ENNReal.ofReal (2 * I.len))).symm

/-! ## Splitting μ into a measurable set and its complement -/

/-- If μ restricted to a measurable set and its complement are μ-Carleson, then μ is μ-Carleson
with constant `C₁ + C₂`.

This is the formal scaffold for a “near/far μ split”: take `S = {p | p.2 ≤ δ}` (near) and `Sᶜ`
(far). Then cite literature for the far regime and isolate the hard near-\(1/2\) regime. -/
lemma MuCarleson.of_restrict_compl
    {μ : Measure (ℝ × ℝ)} {C₁ C₂ : ENNReal} {α : ℝ}
    {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (h₁ : MuCarleson (μ.restrict S) C₁ α)
    (h₂ : MuCarleson (μ.restrict Sᶜ) C₂ α) :
    MuCarleson μ (C₁ + C₂) α := by
  intro I
  set Q : Set (ℝ × ℝ) := carlesonBox I α
  have hQmeas : MeasurableSet Q := measurableSet_carlesonBox (I := I) (α := α)

  -- Partition `Q = (Q ∩ S) ⊔ (Q ∩ Sᶜ)` and use additivity.
  have hdisj : Disjoint (Q ∩ S) (Q ∩ Sᶜ) := by
    refine disjoint_left.2 ?_
    intro p hp1 hp2
    exact hp2.2 hp1.2
  have hmeas2 : MeasurableSet (Q ∩ Sᶜ) := hQmeas.inter hS.compl
  have hEq : Q = (Q ∩ S) ∪ (Q ∩ Sᶜ) := by
    ext p
    by_cases hpS : p ∈ S <;> simp [Q, hpS]

  have hsplit : μ Q = μ (Q ∩ S) + μ (Q ∩ Sᶜ) := by
    -- Use `congrArg` to rewrite `μ Q` by `hEq`, avoiding heavy `simp` (can hit recursion limits).
    have hEqμ : μ Q = μ ((Q ∩ S) ∪ (Q ∩ Sᶜ)) := congrArg (fun A => μ A) hEq
    -- `measure_union` here only needs measurability of the second set.
    have hU : μ ((Q ∩ S) ∪ (Q ∩ Sᶜ)) = μ (Q ∩ S) + μ (Q ∩ Sᶜ) :=
      measure_union (μ := μ) hdisj hmeas2
    exact hEqμ.trans hU

  -- Rewrite intersections as restricted measures on `Q`.
  have hR1 : (μ.restrict S) Q = μ (Q ∩ S) := by
    -- `μ.restrict S Q = μ(Q ∩ S)`
    rw [Measure.restrict_apply' hS]
  have hR2 : (μ.restrict Sᶜ) Q = μ (Q ∩ Sᶜ) := by
    rw [Measure.restrict_apply' hS.compl]

  have h1Q : (μ.restrict S) Q ≤ C₁ * ENNReal.ofReal (2 * I.len) := by
    simpa [Q] using (h₁ I)
  have h2Q : (μ.restrict Sᶜ) Q ≤ C₂ * ENNReal.ofReal (2 * I.len) := by
    simpa [Q] using (h₂ I)

  -- Combine.
  calc
    μ (carlesonBox I α)
        = μ Q := rfl
    _ = (μ.restrict S) Q + (μ.restrict Sᶜ) Q := by
          -- use the partition + rewrite each intersection as a restricted-measure value
          have hR1' : μ (Q ∩ S) = (μ.restrict S) Q := hR1.symm
          have hR2' : μ (Q ∩ Sᶜ) = (μ.restrict Sᶜ) Q := hR2.symm
          have hsum :
              μ (Q ∩ S) + μ (Q ∩ Sᶜ) = (μ.restrict S) Q + (μ.restrict Sᶜ) Q := by
            simp [hR1', hR2']
          have : μ Q = (μ.restrict S) Q + (μ.restrict Sᶜ) Q := by
            calc
              μ Q = μ (Q ∩ S) + μ (Q ∩ Sᶜ) := hsplit
              _ = (μ.restrict S) Q + (μ.restrict Sᶜ) Q := hsum
          exact this
    _ ≤ C₁ * ENNReal.ofReal (2 * I.len) + C₂ * ENNReal.ofReal (2 * I.len) := add_le_add h1Q h2Q
    _ = (C₁ + C₂) * ENNReal.ofReal (2 * I.len) := by
          simpa using (add_mul C₁ C₂ (ENNReal.ofReal (2 * I.len))).symm

end RiemannRecognitionGeometry
