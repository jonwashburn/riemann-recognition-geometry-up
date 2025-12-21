/-
# Dyadic Carleson boxes and annuli (Route A geometry scaffold)

This file implements the purely geometric objects used in the Route‑A tail-energy proof skeleton:
dyadic dilations of a Whitney base interval, the associated Carleson boxes `Q_j`, and the dyadic
annuli `A_j = Q_{j+1} \\ Q_j`.

The goal is to make the annulus decomposition *executable in Lean* without committing to any
arithmetic estimates (those live in μ-Carleson / explicit-formula inputs).
-/

import RiemannRecognitionGeometry.CarlesonBound

noncomputable section

namespace RiemannRecognitionGeometry

open Real MeasureTheory Set

/-! ## Dyadic dilations of a Whitney interval -/

/-- Dyadic dilation of a Whitney interval: multiply the half-length by `2^j`, keep the center fixed. -/
def dyadicDilate (I : WhitneyInterval) (j : ℕ) : WhitneyInterval :=
  { t0 := I.t0
    len := (2 : ℝ)^j * I.len
    len_pos := by
      have h2 : (0 : ℝ) < 2 := by norm_num
      have hpow : 0 < (2 : ℝ)^j := pow_pos h2 j
      exact mul_pos hpow I.len_pos }

/-- The canonical Carleson box `Q_j` associated to `I` at dyadic level `j` (aperture fixed to 2).

With `I = (t0,L)`, `Qbox I j` has:
- horizontal span `|γ - t0| ≤ 2^j·L`
- vertical height `0 < σ ≤ 2^(j+2)·L` (since aperture 2 gives height `4·(2^j·L)`). -/
def Qbox (I : WhitneyInterval) (j : ℕ) : Set (ℝ × ℝ) :=
  carlesonBox (dyadicDilate I j) 2

/-- The dyadic annulus `A_j := Q_{j+1} \\ Q_j`. -/
def Abox (I : WhitneyInterval) (j : ℕ) : Set (ℝ × ℝ) :=
  Qbox I (j+1) \ Qbox I j

/-! ## Basic set-theoretic facts -/

lemma Abox_subset_Qbox_succ (I : WhitneyInterval) (j : ℕ) : Abox I j ⊆ Qbox I (j+1) := by
  intro p hp
  exact hp.1

lemma Abox_disjoint_Qbox (I : WhitneyInterval) (j : ℕ) : Disjoint (Abox I j) (Qbox I j) := by
  refine disjoint_left.2 ?_
  intro p hpA hpQ
  exact hpA.2 hpQ

lemma Qbox_mono (I : WhitneyInterval) (j : ℕ) : Qbox I j ⊆ Qbox I (j+1) := by
  intro p hp
  rcases hp with ⟨hp_int, hpσ_pos, hpσ_le⟩
  refine ⟨?_, hpσ_pos, ?_⟩
  · -- interval monotonicity under dyadic dilation
    -- membership is `p.1 ∈ Icc (t0-len) (t0+len)`
    have hmem :
        p.1 ∈ Set.Icc ((dyadicDilate I j).t0 - (dyadicDilate I j).len)
                      ((dyadicDilate I j).t0 + (dyadicDilate I j).len) := by
      simpa [WhitneyInterval.interval, Qbox, carlesonBox] using hp_int
    rcases hmem with ⟨hl, hr⟩
    have hpow : (2 : ℝ)^j ≤ (2 : ℝ)^(j+1) := by
      -- `2^j ≤ 2^(j+1) = 2^j * 2`
      have ha : 0 ≤ (2 : ℝ)^j := le_of_lt (pow_pos (by norm_num : (0:ℝ) < 2) j)
      have h : (2 : ℝ)^j ≤ (2 : ℝ)^j * 2 := by nlinarith [ha]
      -- rewrite the goal’s RHS using `pow_succ`, then close with `h`
      have hx : (2 : ℝ)^(j+1) = (2 : ℝ)^j * 2 := by
        simp [pow_succ, mul_assoc, mul_comm, mul_left_comm]
      -- after rewriting, the goal is exactly `h`
      -- avoid `simpa` (unnecessarySimpa linter)
      rw [hx]
      exact h
    -- now enlarge the interval bounds
    have hl' : (I.t0 - (2 : ℝ)^(j+1) * I.len) ≤ p.1 := by
      -- from `I.t0 - 2^j*L ≤ p.1` and `2^(j+1) ≥ 2^j`
      have : I.t0 - (2 : ℝ)^j * I.len ≤ p.1 := by
        simpa [dyadicDilate] using hl
      have hbound : I.t0 - (2 : ℝ)^(j+1) * I.len ≤ I.t0 - (2 : ℝ)^j * I.len := by
        have hL : 0 ≤ I.len := le_of_lt I.len_pos
        nlinarith [hpow, hL]
      exact le_trans hbound this
    have hr' : p.1 ≤ I.t0 + (2 : ℝ)^(j+1) * I.len := by
      have : p.1 ≤ I.t0 + (2 : ℝ)^j * I.len := by
        simpa [dyadicDilate] using hr
      have hbound : I.t0 + (2 : ℝ)^j * I.len ≤ I.t0 + (2 : ℝ)^(j+1) * I.len := by
        have hL : 0 ≤ I.len := le_of_lt I.len_pos
        nlinarith [hpow, hL]
      exact le_trans this hbound
    -- pack back into interval membership for the larger dilation
    have : p.1 ∈ (dyadicDilate I (j+1)).interval := by
      simp [WhitneyInterval.interval, dyadicDilate, Set.mem_Icc, hl', hr']
    simpa [Qbox, carlesonBox] using this
  · -- vertical bound monotonicity: height grows with `j`
    -- from `p.2 ≤ 4*(2^j*L)` infer `p.2 ≤ 4*(2^(j+1)*L)`
    have : p.2 ≤ 2 * (2 * (dyadicDilate I j).len) := by
      simpa [Qbox, carlesonBox] using hpσ_le
    have hlen : (dyadicDilate I j).len ≤ (dyadicDilate I (j+1)).len := by
      simp [dyadicDilate, pow_succ, mul_assoc, mul_left_comm, mul_comm]
      have hL : 0 ≤ I.len := le_of_lt I.len_pos
      have hpow' : (2 : ℝ)^j ≤ (2 : ℝ)^j * 2 := by
        have ha : 0 ≤ (2 : ℝ)^j := le_of_lt (pow_pos (by norm_num : (0:ℝ)<2) j)
        nlinarith [ha]
      nlinarith [hpow', hL]
    have hheight :
        2 * (2 * (dyadicDilate I j).len) ≤ 2 * (2 * (dyadicDilate I (j+1)).len) := by
      nlinarith [hlen]
    have : p.2 ≤ 2 * (2 * (dyadicDilate I (j+1)).len) := le_trans this hheight
    simpa [Qbox, carlesonBox] using this

lemma Qbox_mono_le (I : WhitneyInterval) {m n : ℕ} (hmn : m ≤ n) : Qbox I m ⊆ Qbox I n := by
  -- iterate the one-step monotonicity lemma
  induction hmn with
  | refl =>
      intro p hp
      exact hp
  | step hmn ih =>
      intro p hp
      exact Qbox_mono I _ (ih hp)

lemma Abox_disjoint_of_lt (I : WhitneyInterval) {j₁ j₂ : ℕ} (h : j₁ < j₂) :
    Disjoint (Abox I j₁) (Abox I j₂) := by
  refine disjoint_left.2 ?_
  intro p hp₁ hp₂
  -- `p ∈ Abox I j₁` gives `p ∈ Qbox I (j₁+1)`
  have hpQ : p ∈ Qbox I (j₁+1) := hp₁.1
  -- since `j₁+1 ≤ j₂`, we get `p ∈ Qbox I j₂`
  have hj : j₁ + 1 ≤ j₂ := Nat.succ_le_of_lt h
  have hpQ2 : p ∈ Qbox I j₂ := (Qbox_mono_le I hj) hpQ
  -- but `p ∈ Abox I j₂` implies `p ∉ Qbox I j₂`
  exact hp₂.2 hpQ2

lemma Abox_pairwise_disjoint (I : WhitneyInterval) :
    Pairwise (fun j₁ j₂ : ℕ => Disjoint (Abox I j₁) (Abox I j₂)) := by
  intro j₁ j₂ hj
  rcases lt_or_gt_of_ne hj with hlt | hgt
  · exact Abox_disjoint_of_lt I hlt
  · have h' : Disjoint (Abox I j₂) (Abox I j₁) := Abox_disjoint_of_lt I hgt
    simpa [disjoint_comm] using h'

end RiemannRecognitionGeometry
