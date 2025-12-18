import Mathlib.Data.Complex.Trigonometric
import RiemannRecognitionGeometry.ExplicitFormula.OuterConstruction

/-!
# (P+) boundary positivity core API

This module isolates the **boundary positivity** predicate used in the Route‑B / pinch route:

`(P+) : ∀ᵐ t, 0 ≤ Re( F_pinch(det2,O,ξ) (boundary t) )`

and provides a small but important rewrite: if the boundary trace of the PSC ratio has the
form `J(boundary t) = exp(i·θ(t))`, then `(P+)` is equivalent to `cos(θ(t)) ≥ 0` a.e.

This is exactly the “phase argument” choke‑point.

It mirrors `rh/RS/WhitneyAeCore.lean` in `riemann-finish`, but is parameterized (no canonical `O`)
and lives in the Route‑3 namespace.
-/

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

namespace PPlusCore

open Complex MeasureTheory Filter
open scoped Real

/-- `(P+)` for a pinch field: boundary real-part nonnegativity a.e. -/
def PPlus_holds (det2 O ξ : ℂ → ℂ) : Prop :=
  ∀ᵐ t : ℝ, 0 ≤ ((OuterConstruction.F_pinch det2 O ξ) (OuterConstruction.boundary t)).re

/-- Helper: `Re(2 * exp(i·θ)) = 2 * cos(θ)` for real `θ`. -/
lemma re_two_mul_exp_I_mul_real (θ : ℝ) :
    (((2 : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).re) = (2 : ℝ) * Real.cos θ := by
  -- Expand `exp (θ * I)` in terms of cos/sin, then read off the real part.
  have hexp : Complex.exp ((θ : ℂ) * Complex.I) = Complex.cos θ + Complex.sin θ * Complex.I := by
    simpa using (Complex.exp_mul_I (x := (θ : ℂ)))
  -- Rewrite `I * θ` as `θ * I` to use the lemma above.
  have hcomm : (Complex.I * (θ : ℂ)) = (θ : ℂ) * Complex.I := by ring
  -- Now compute real parts.
  calc
    (((2 : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).re)
        = (((2 : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).re) := by
            simp [hcomm]
    _ = (((2 : ℂ) * (Complex.cos θ + Complex.sin θ * Complex.I)).re) := by
            simp [hexp]
    _ = ((2 : ℂ).re) * (Complex.cos θ + Complex.sin θ * Complex.I).re
          - ((2 : ℂ).im) * (Complex.cos θ + Complex.sin θ * Complex.I).im := by
            simpa using (Complex.mul_re (2 : ℂ) (Complex.cos θ + Complex.sin θ * Complex.I))
    _ = (2 : ℝ) * (Complex.cos θ).re := by
            simp
    _ = (2 : ℝ) * Real.cos θ := by
            simpa using (Complex.cos_ofReal_re θ)

/--
If the PSC ratio `J := det2/(O·ξ)` has boundary phase representation
`J(boundary t) = exp(i·θ(t))` a.e., then `(P+)` is exactly `cos(θ(t)) ≥ 0` a.e.
-/
theorem PPlus_holds_iff_cos_nonneg_of_phase
    (det2 O ξ : ℂ → ℂ) (θ : ℝ → ℝ)
    (hPhase :
      ∀ᵐ t : ℝ,
        OuterConstruction.J_pinch det2 O ξ (OuterConstruction.boundary t) =
          Complex.exp (Complex.I * (θ t : ℂ))) :
    PPlus_holds det2 O ξ ↔ (∀ᵐ t : ℝ, 0 ≤ Real.cos (θ t)) := by
  -- Unfold (P+) and rewrite `F_pinch = 2*J_pinch` using the phase representation.
  change
      (∀ᵐ t : ℝ,
        0 ≤ ((2 : ℂ) * OuterConstruction.J_pinch det2 O ξ (OuterConstruction.boundary t)).re)
        ↔ (∀ᵐ t : ℝ, 0 ≤ Real.cos (θ t))
  constructor
  · intro hP
    -- Combine `hP` with `hPhase` pointwise.
    filter_upwards [hP, hPhase] with t htP htPhase
    -- Replace `J_pinch` by the phase expression.
    have hEq : ((2 : ℂ) * OuterConstruction.J_pinch det2 O ξ (OuterConstruction.boundary t)).re
        = (((2 : ℂ) * Complex.exp (Complex.I * (θ t : ℂ))).re) := by
          exact congrArg (fun z : ℂ => ((2 : ℂ) * z).re) htPhase
    -- Now compute the RHS.
    have hre : (((2 : ℂ) * Complex.exp (Complex.I * (θ t : ℂ))).re) =
        (2 : ℝ) * Real.cos (θ t) := re_two_mul_exp_I_mul_real (θ t)
    -- Conclude `0 ≤ cos`.
    have hcos2 : 0 ≤ (2 : ℝ) * Real.cos (θ t) := by
      -- Step 1: from `htP` and `hEq`, get boundary positivity for the phase expression.
      have hExp : 0 ≤ (((2 : ℂ) * Complex.exp (Complex.I * (θ t : ℂ))).re) := by
        -- Rewrite the goal back to `htP` using `hEq`.
        rw [← hEq]
        exact htP
      -- Step 2: convert `Re(2·exp(iθ)) ≥ 0` into `2·cos(θ) ≥ 0` using `hre`.
      -- (Avoid `simp` here: it tends to cancel the positive factor 2.)
      rw [← hre]
      exact hExp
    -- Divide by `2 > 0`.
    have h2pos : (0 : ℝ) < 2 := by norm_num
    -- Use the form `cos * 2` to match `nonneg_of_mul_nonneg_left`.
    have h' : 0 ≤ Real.cos (θ t) * 2 := by simpa [mul_comm] using hcos2
    exact nonneg_of_mul_nonneg_left h' h2pos
  · intro hCos
    filter_upwards [hCos, hPhase] with t htCos htPhase
    -- Compute real part using the phase representation and the explicit formula.
    have hre :
        ((2 : ℂ) * OuterConstruction.J_pinch det2 O ξ (OuterConstruction.boundary t)).re
          = (2 : ℝ) * Real.cos (θ t) := by
      calc
        ((2 : ℂ) * OuterConstruction.J_pinch det2 O ξ (OuterConstruction.boundary t)).re
            = ((2 : ℂ) * Complex.exp (Complex.I * (θ t : ℂ))).re := by
                exact congrArg (fun z : ℂ => ((2 : ℂ) * z).re) htPhase
        _ = (2 : ℝ) * Real.cos (θ t) := re_two_mul_exp_I_mul_real (θ t)
    -- Now `0 ≤ 2*cos` from `0 ≤ cos`.
    have hcos2 : 0 ≤ (2 : ℝ) * Real.cos (θ t) := mul_nonneg (by norm_num) htCos
    -- Rewrite the goal (a boundary real-part inequality) into `0 ≤ 2*cos` via `hre`,
    -- then close by `hcos2`. (Avoid `simp` cancellation.)
    -- Goal is: 0 ≤ Re(2·J_pinch(boundary t)).
    -- Using `hre` and the phase representation we can rewrite it to `0 ≤ 2*cos(θ t)`.
    -- First, rewrite the goal with `hre`.
    have : 0 ≤ ((2 : ℂ) * OuterConstruction.J_pinch det2 O ξ (OuterConstruction.boundary t)).re := by
      -- rewrite to the `2*cos` inequality
      -- `hre` is: Re(2·J_pinch) = 2*cos
      -- so `rw [hre]` turns the goal into `0 ≤ 2*cos`.
      rw [hre]
      exact hcos2
    exact this

end PPlusCore

end ExplicitFormula
end RiemannRecognitionGeometry
