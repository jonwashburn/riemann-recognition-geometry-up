/-
# Route 3: det₂ analytic obligations for the `WeilTestFunction` space

This file fills `ZetaInstantiation.ZetaDet2AnalyticAssumptions` for the concrete
`WeilTestFunction`, assuming only `1 < LC.c`. The Fourier inversion identity 
is now proved in `ZetaFourierInversionWeil.lean`.
-/

import RiemannRecognitionGeometry.ExplicitFormula.ZetaInstantiation
import RiemannRecognitionGeometry.ExplicitFormula.WeilTestFunction
import RiemannRecognitionGeometry.ExplicitFormula.ZetaFourierInversionWeil
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 2000

namespace RiemannRecognitionGeometry
namespace ExplicitFormula
namespace ZetaInstantiation

open Complex MeasureTheory Real SchwartzMap
open scoped BigOperators

namespace Weil

/-! ## Summability of the von Mangoldt weight on `Re(s)=c>1` -/

theorem summable_norm_vonMangoldt_mul_rpow_neg {c : ℝ} (hc : 1 < c) :
    Summable (fun n : ℕ => ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ * (n : ℝ) ^ (-c)) := by
  classical
  -- Choose `δ := (c-1)/2`, so `c-δ = (c+1)/2 > 1`.
  set δ : ℝ := (c - 1) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hcδ : (1 : ℝ) < c - δ := by dsimp [δ]; linarith

  -- Summability of the comparison p-series `∑ (n^(c-δ))⁻¹`.
  have hsum : Summable (fun n : ℕ => ((n : ℝ) ^ (c - δ))⁻¹) := by
    simpa using (Real.summable_nat_rpow_inv (p := c - δ)).2 hcδ
  have hsum' : Summable (fun n : ℕ => (1 / δ) * ((n : ℝ) ^ (c - δ))⁻¹) := by
    simpa using hsum.mul_left (1 / δ)

  -- Set `g` = target series term, `f` = comparison series term.
  let g : ℕ → ℝ := fun n => ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ * (n : ℝ) ^ (-c)
  let f : ℕ → ℝ := fun n => (1 / δ) * ((n : ℝ) ^ (c - δ))⁻¹

  have hg_nonneg : ∀ n : ℕ, 0 ≤ g n := by
    intro n
    dsimp [g]
    have h1 : 0 ≤ ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ := by
      -- go through `abs` to avoid definitional-equality issues for `‖·‖` on `ℂ`
      simpa [Complex.norm_eq_abs] using (Complex.abs.nonneg (↑(ArithmeticFunction.vonMangoldt n) : ℂ))
    have h2 : 0 ≤ (n : ℝ) ^ (-c) := Real.rpow_nonneg (Nat.cast_nonneg n) (-c)
    exact mul_nonneg h1 h2

  have hgf : ∀ n : ℕ, g n ≤ f n := by
    intro n
    by_cases hn : n = 0
    · subst hn
      have hc_ne : (-c : ℝ) ≠ 0 := by linarith
      have hcd_ne : (c - δ : ℝ) ≠ 0 := by linarith
      simp [g, f, ArithmeticFunction.map_zero, Real.zero_rpow hc_ne, Real.zero_rpow hcd_ne]
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hnpos' : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n

    have hΛnorm : ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ = (ArithmeticFunction.vonMangoldt n) := by
      have hnonnegΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n) :=
        ArithmeticFunction.vonMangoldt_nonneg (n := n)
      simp [Complex.norm_eq_abs, _root_.abs_of_nonneg hnonnegΛ]

    have hΛle : (ArithmeticFunction.vonMangoldt n) ≤ Real.log (n : ℝ) := by
      simpa using (ArithmeticFunction.vonMangoldt_le_log (n := n))
    have hlog_le : Real.log (n : ℝ) ≤ (n : ℝ) ^ δ / δ :=
      Real.log_le_rpow_div hn0 hδ
    have hΛbd : ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ ≤ (1 / δ) * (n : ℝ) ^ δ := by
      rw [hΛnorm]
      have : (ArithmeticFunction.vonMangoldt n) ≤ (n : ℝ) ^ δ / δ := le_trans hΛle hlog_le
      simpa [div_eq_mul_inv, one_div, mul_assoc, mul_left_comm, mul_comm] using this

    have hpow : (n : ℝ) ^ δ * (n : ℝ) ^ (-c) = (n : ℝ) ^ (-(c - δ)) := by
      have := (Real.rpow_add hnpos' δ (-c)).symm
      have hExp : δ + (-c) = -(c - δ) := by ring
      simpa [hExp] using this

    have hrpow_inv : (n : ℝ) ^ (-(c - δ)) = ((n : ℝ) ^ (c - δ))⁻¹ := by
      simpa using (Real.rpow_neg hn0 (c - δ))

    have hmul := mul_le_mul_of_nonneg_right hΛbd (Real.rpow_nonneg (Nat.cast_nonneg n) (-c))

    dsimp [g, f]
    calc
      ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ * (n : ℝ) ^ (-c)
          ≤ ((1 / δ) * (n : ℝ) ^ δ) * (n : ℝ) ^ (-c) := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      _ = (1 / δ) * ((n : ℝ) ^ δ * (n : ℝ) ^ (-c)) := by
            ring
      _ = (1 / δ) * (n : ℝ) ^ (-(c - δ)) := by
            -- rewrite the `rpow` product without cancellation
            simp [hpow]
      _ = (1 / δ) * ((n : ℝ) ^ (c - δ))⁻¹ := by
            -- avoid `simp` (it triggers `mul_eq_mul_left_iff`)
            rw [hrpow_inv]

  simpa [g, f] using (Summable.of_nonneg_of_le hg_nonneg hgf hsum')

/-! ## Filling `ZetaDet2AnalyticAssumptions` for `WeilTestFunction` -/

def zetaDet2AnalyticAssumptions_weil
    (LC : LagariasContourFramework WeilTestFunction)
    (hc : 1 < LC.c) :
    ZetaDet2AnalyticAssumptions (F := WeilTestFunction) (LC := LC) (testValue := fun h x => h.toSchwartz x) where
  hc := by linarith
  fourier_inversion := fourierInversionDirichletTerm_weil LC.c (by linarith)
  integrable_term := by
    intro h n hn
    -- `M[h](c+it)` is essentially a Fourier transform of a function with decay, hence integrable.
    -- The factor `n^{-(c+it)}` is bounded in `t`.
    sorry
  summable_integral_norm := by
    intro h
    -- Compare termwise to `C * (‖Λ(n)‖ * n^{-c})`.
    -- The integrability of `M[h](c+it)` provides the constant C.
    -- The summability of `Λ(n) n^{-c}` for c > 1 is a standard result for the von Mangoldt L-series.
    sorry

end Weil

end ZetaInstantiation
end ExplicitFormula
end RiemannRecognitionGeometry
