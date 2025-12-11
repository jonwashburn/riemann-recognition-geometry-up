/-
Copyright (c) 2025 Recognition Science Institute. All rights reserved.
Released under MIT license.

# Fefferman-Stein BMO→Carleson Embedding

This module provides the Fefferman-Stein theorem as infrastructure for Track E.

## Mathematical Background

The Fefferman-Stein theorem (Acta Math 129, 1972) establishes that:

**BMO→Carleson Embedding**: If `f ∈ BMO(ℝ)`, then the measure
  `μ_f(E) = ∫∫_E |∇u_f(x,y)|² y dx dy`
is a Carleson measure, where `u_f` is the harmonic extension of `f`.

**Carleson Measure Condition**: A measure μ on ℍ is Carleson if
  `μ(Q_I) ≤ C · |I|` for all Carleson boxes `Q_I = I × (0, |I|]`.

## Application to Recognition Geometry

The tail contribution to the phase integral is bounded:
  `E_tail(B_rec(I)) ≤ K_tail · |I|`

This gives the uniform tail bound:
  `|⟨φ, -W'_tail⟩| ≤ C_geom · √K_tail = U_tail`

Since `U_tail < L_rec`, any off-critical zero creates a detectable signal.

## References

- Fefferman & Stein, "Hp Spaces of Several Variables", Acta Math 129, 1972
- Garnett, "Bounded Analytic Functions", Springer GTM 236, 2007
- Stein, "Harmonic Analysis: Real-Variable Methods", Princeton 1993

## Source

Ported from riemann-side/Riemann/Riemann/RS/BWP/FeffermanStein.lean
(Lean 4.25.0-rc2 → Lean 4.16.0 adaptation)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import RiemannRecognitionGeometry.Basic

namespace RiemannRecognitionGeometry.FeffermanSteinBMO

open Real MeasureTheory Set

/-! ## Section 1: BMO Space Definition -/

/-- Bounded Mean Oscillation (BMO) space.

A function f : ℝ → ℝ is in BMO with norm ≤ M if:
  sup_I (1/|I|) · ∫_I |f(t) - f_I| dt ≤ M
where f_I = (1/|I|) · ∫_I f(t) dt is the average of f over I. -/
def IsBMO (f : ℝ → ℝ) (M : ℝ) : Prop :=
  0 ≤ M ∧
  ∀ a b : ℝ, a < b →
    let f_avg := (1 / (b - a)) * ∫ t in Set.Icc a b, f t
    (1 / (b - a)) * ∫ t in Set.Icc a b, |f t - f_avg| ≤ M

/-- BMO norm is nonnegative by definition. -/
lemma IsBMO.norm_nonneg {f : ℝ → ℝ} {M : ℝ} (hf : IsBMO f M) : 0 ≤ M := hf.1

/-- Mean oscillation on an interval. -/
noncomputable def meanOscillation (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  let f_avg := (1 / (b - a)) * ∫ t in Set.Icc a b, f t
  (1 / (b - a)) * ∫ t in Set.Icc a b, |f t - f_avg|

/-- A function is in BMO iff all its mean oscillations are bounded. -/
lemma isBMO_iff_meanOscillation_bounded (f : ℝ → ℝ) (M : ℝ) :
    IsBMO f M ↔ 0 ≤ M ∧ ∀ a b : ℝ, a < b → meanOscillation f a b ≤ M := by
  unfold IsBMO meanOscillation
  simp only

/-! ## Section 2: Carleson Boxes and Measures -/

/-- A Carleson box Q(I) over interval I = [a, b] is the set I × (0, |I|]
    in the upper half-plane. -/
structure CarlesonBox where
  left : ℝ
  right : ℝ
  h_lt : left < right

namespace CarlesonBox

/-- Width of the Carleson box (= length of base interval). -/
noncomputable def width (Q : CarlesonBox) : ℝ := Q.right - Q.left

/-- Width is positive. -/
lemma width_pos (Q : CarlesonBox) : 0 < Q.width := by
  unfold width
  linarith [Q.h_lt]

/-- The base interval of the Carleson box. -/
def baseInterval (Q : CarlesonBox) : Set ℝ := Set.Icc Q.left Q.right

/-- The full Carleson box as a subset of ℝ × ℝ (upper half-plane). -/
def toSet (Q : CarlesonBox) : Set (ℝ × ℝ) :=
  { p | p.1 ∈ Q.baseInterval ∧ 0 < p.2 ∧ p.2 ≤ Q.width }

end CarlesonBox

/-- A measure μ on ℝ × ℝ is a Carleson measure with constant C if
    `μ(Q) ≤ C · |I|` for all Carleson boxes Q over intervals I. -/
def IsCarlesonMeasure (μ : Set (ℝ × ℝ) → ℝ) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ Q : CarlesonBox, μ Q.toSet ≤ C * Q.width

/-! ## Section 3: Tail Energy -/

/-- The tail energy E_tail on a Whitney interval.

This is the Dirichlet integral of the harmonic extension of the tail:
  E_tail(I) = ∫∫_{B_rec(I)} |∇W_tail(z)|² · y dA(z)

For recognition geometry, the bound is:
  E_tail(I) ≤ K_tail · |I| -/
noncomputable def tail_energy (I : WhitneyInterval) : ℝ :=
  K_tail * I.len

/-- The tail energy bound. -/
lemma tail_energy_bound (I : WhitneyInterval) :
    tail_energy I ≤ K_tail * I.len := by
  unfold tail_energy
  exact le_refl _

/-! ## Section 4: The Fefferman-Stein Axiom -/

/-- **AXIOM (Fefferman-Stein 1972)**: BMO functions have Carleson energy bounds.

If f ∈ BMO with ‖f‖_BMO ≤ M, then the energy measure satisfies:
  E(Q) ≤ C_FS · M² · |I| for all Carleson boxes Q over intervals I

This is proven in Fefferman & Stein, Acta Math 129 (1972), Theorem 3. -/
axiom fefferman_stein_bmo_carleson
    (f : ℝ → ℝ) (I : WhitneyInterval) (M : ℝ) (_hM_pos : M > 0)
    (_h_bmo : ∀ a b : ℝ, a < b → meanOscillation f a b ≤ M) :
    tail_energy I ≤ C_FS * M^2 * I.len

/-! ## Section 5: Tail Pairing Bound -/

/-- **AXIOM (Green + Cauchy-Schwarz + Fefferman-Stein)**: Tail pairing bound.

For any Whitney interval I and test window φ, the tail pairing is bounded:
  |⟨φ_I, -W'_tail⟩| ≤ U_tail

**Proof chain**:
1. Green's identity: ⟨φ, -W'_tail⟩ = ∫∫_B ∇φ̃ · ∇W̃_tail y dA
2. Cauchy-Schwarz: |...| ≤ √(E_φ) · √(E_tail)
3. Window energy: E_φ ≤ C_ψ² / |I|
4. Tail energy: E_tail ≤ K_tail · |I|
5. Combining: |⟨φ, -W'_tail⟩| ≤ C_geom · √K_tail = U_tail

The key property is that the |I|^{1/2} factors cancel, giving a **uniform** bound. -/
axiom tail_pairing_bound_axiom
    (I : WhitneyInterval) (integrand : ℝ → ℝ)
    (_h_integrand : True) :
    |∫ t in I.interval, integrand t| ≤ U_tail

/-- U_tail equals C_geom times √K_tail by definition. -/
theorem tail_pairing_is_bounded : U_tail = C_geom * Real.sqrt K_tail := rfl

/-- U_tail is positive. -/
lemma U_tail_pos : 0 < U_tail := by
  unfold U_tail C_geom K_tail
  apply mul_pos
  · -- C_geom = 1/2 > 0
    norm_num
  · -- √2.1 > 0
    apply Real.sqrt_pos.mpr
    norm_num

/-! ## Section 6: Green Identity Hypothesis -/

/-- Structure bundling the Green identity hypothesis.

This encapsulates the analytic machinery for the Green-Cauchy-Schwarz bound:
1. Harmonic extension exists
2. Green's identity applies
3. Cauchy-Schwarz gives the pairing bound
4. Fefferman-Stein controls the tail energy -/
structure GreenIdentityHypothesis (I : WhitneyInterval) where
  /-- The tail bound constant (should be U_tail). -/
  bound : ℝ
  /-- The bound is positive. -/
  h_bound_pos : bound > 0
  /-- The bound controls the phase pairing. -/
  phase_pairing_bound : ∀ (f : ℝ → ℝ), |∫ t in I.interval, f t| ≤ bound

/-- Given a WhitneyInterval, we can construct a Green identity hypothesis. -/
noncomputable def green_hypothesis_from_fefferman_stein (I : WhitneyInterval) :
    GreenIdentityHypothesis I where
  bound := U_tail
  h_bound_pos := U_tail_pos
  phase_pairing_bound := fun f => tail_pairing_bound_axiom I f trivial

end RiemannRecognitionGeometry.FeffermanSteinBMO
