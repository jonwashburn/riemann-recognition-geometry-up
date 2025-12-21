/-
# Measurability and measure bookkeeping for dyadic Carleson boxes/annuli (Route A scaffold)

This module complements `DyadicCarlesonAnnuli.lean` by providing:
- measurability of `carlesonBox`, hence of `Qbox`/`Abox`,
- the disjoint-union identity `Q_{j+1} = Q_j ⊔ A_j`,
- and the corresponding measure identity `μ(Q_{j+1}) = μ(Q_j) + μ(A_j)`.

These are the structural ingredients used when turning the annulus decomposition in the B2′ plan
into an actual Lean proof skeleton.
-/

import RiemannRecognitionGeometry.DyadicCarlesonAnnuli

noncomputable section

namespace RiemannRecognitionGeometry

open Real MeasureTheory Set

/-! ## Measurability -/

lemma measurableSet_carlesonBox (I : WhitneyInterval) (α : ℝ := 2) :
    MeasurableSet (carlesonBox I α) := by
  -- rewrite as an intersection of three measurable sets
  have hI : MeasurableSet I.interval := by
    -- `I.interval = Icc (t0-L) (t0+L)` is closed, hence measurable
    simp [WhitneyInterval.interval]
  have h1 : MeasurableSet {p : ℝ × ℝ | p.1 ∈ I.interval} := by
    -- `{p | p.1 ∈ I.interval} = Prod.fst ⁻¹' I.interval`
    simpa [Set.preimage, Set.mem_setOf_eq] using hI.preimage measurable_fst
  have h2 : MeasurableSet {p : ℝ × ℝ | (0 : ℝ) < p.2} :=
    measurableSet_lt measurable_const measurable_snd
  have h3 : MeasurableSet {p : ℝ × ℝ | p.2 ≤ α * (2 * I.len)} :=
    measurableSet_le measurable_snd measurable_const
  have hinter : MeasurableSet ({p : ℝ × ℝ | p.1 ∈ I.interval} ∩ ({p : ℝ × ℝ | (0 : ℝ) < p.2} ∩ {p : ℝ × ℝ | p.2 ≤ α * (2 * I.len)})) :=
    h1.inter (h2.inter h3)
  have hEq :
      carlesonBox I α =
        {p : ℝ × ℝ | p.1 ∈ I.interval} ∩ ({p : ℝ × ℝ | (0 : ℝ) < p.2} ∩ {p : ℝ × ℝ | p.2 ≤ α * (2 * I.len)}) := by
    ext p
    simp [carlesonBox, and_assoc, and_left_comm, and_comm]
  simpa [hEq] using hinter

lemma measurableSet_Qbox (I : WhitneyInterval) (j : ℕ) : MeasurableSet (Qbox I j) := by
  simpa [Qbox] using (measurableSet_carlesonBox (I := dyadicDilate I j) (α := 2))

lemma measurableSet_Abox (I : WhitneyInterval) (j : ℕ) : MeasurableSet (Abox I j) := by
  -- `Abox I j = Qbox I (j+1) \ Qbox I j`
  simpa [Abox] using (measurableSet_Qbox I (j+1)).diff (measurableSet_Qbox I j)

/-! ## Disjoint union identity -/

lemma Qbox_succ_eq_union (I : WhitneyInterval) (j : ℕ) :
    Qbox I (j+1) = Qbox I j ∪ Abox I j := by
  classical
  ext p
  constructor
  · intro hp
    by_cases h : p ∈ Qbox I j
    · exact Or.inl h
    · exact Or.inr ⟨hp, h⟩
  · intro hp
    rcases hp with hp | hp
    · exact Qbox_mono I j hp
    · exact hp.1

lemma measure_Qbox_succ (μ : Measure (ℝ × ℝ)) (I : WhitneyInterval) (j : ℕ) :
    μ (Qbox I (j+1)) = μ (Qbox I j) + μ (Abox I j) := by
  have hdisj : Disjoint (Qbox I j) (Abox I j) := (Abox_disjoint_Qbox I j).symm
  have hmeasQ : MeasurableSet (Qbox I j) := measurableSet_Qbox I j
  have hmeasA : MeasurableSet (Abox I j) := measurableSet_Abox I j
  -- rewrite `Qbox I (j+1)` as a disjoint union
  have hEq : Qbox I (j+1) = Qbox I j ∪ Abox I j := Qbox_succ_eq_union I j
  -- measure additivity on disjoint measurable unions
  -- `measure_union` in this environment only needs measurability of the second set.
  simpa [hEq] using (measure_union hdisj hmeasA)

/-! ## Telescoping sums over annuli -/

/-- Telescoping identity for the dyadic decomposition:

`μ(Q_{K+m}) = μ(Q_K) + ∑_{t=0}^{m-1} μ(A_{K+t})`.

This is the precise “sum over disjoint annuli” step used in the Route‑A tail-energy skeleton. -/
lemma measure_Qbox_eq_measure_Qbox_add_sum_Abox_shift
    (μ : Measure (ℝ × ℝ)) (I : WhitneyInterval) (K m : ℕ) :
    μ (Qbox I (K + m)) =
      μ (Qbox I K) + (Finset.range m).sum (fun t => μ (Abox I (K + t))) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      -- recursion step: `Q_{K+m+1} = Q_{K+m} ⊔ A_{K+m}`
      have hrec :
          μ (Qbox I (K + (m+1))) = μ (Qbox I (K + m)) + μ (Abox I (K + m)) := by
        -- `measure_Qbox_succ` at index `K+m`
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (measure_Qbox_succ (μ := μ) (I := I) (j := K + m))
      -- unwind the sum over `range (m+1)`
      have hsum :
          (Finset.range (m+1)).sum (fun t => μ (Abox I (K + t))) =
            (Finset.range m).sum (fun t => μ (Abox I (K + t))) + μ (Abox I (K + m)) := by
        -- `Finset.sum_range_succ` with `f t := μ (Abox I (K+t))`
        simpa [Nat.add_assoc] using
          (Finset.sum_range_succ (fun t => μ (Abox I (K + t))) m)
      -- combine
      calc
        μ (Qbox I (K + (m+1)))
            = μ (Qbox I (K + m)) + μ (Abox I (K + m)) := hrec
        _ = (μ (Qbox I K) + (Finset.range m).sum (fun t => μ (Abox I (K + t)))) + μ (Abox I (K + m)) := by
              simp [ih, Nat.add_assoc]
        _ = μ (Qbox I K) + (((Finset.range m).sum (fun t => μ (Abox I (K + t)))) + μ (Abox I (K + m))) := by
              ac_rfl
        _ = μ (Qbox I K) + ((Finset.range (m+1)).sum (fun t => μ (Abox I (K + t)))) := by
              simp [hsum, add_assoc]

/-- Special case of the telescoping identity starting at `K = 0`. -/
lemma measure_Qbox_eq_measure_Qbox_zero_add_sum_Abox
    (μ : Measure (ℝ × ℝ)) (I : WhitneyInterval) (n : ℕ) :
    μ (Qbox I n) = μ (Qbox I 0) + (Finset.range n).sum (fun j => μ (Abox I j)) := by
  simpa using (measure_Qbox_eq_measure_Qbox_add_sum_Abox_shift (μ := μ) (I := I) (K := 0) (m := n))

end RiemannRecognitionGeometry
