/-!
# Port step: RG-facing “Blaschke dominates total” via the cofactor tail bound route

The existing RG theorem `Axioms.blaschke_dominates_total` currently depends on:

- `RGAssumptions` (an RG-specific “energy budget” bundle), and
- the derived tail bound `Conjectures.weierstrass_tail_bound_axiom_statement`.

Using the Port pipeline, we can obtain the same tail bound from:

- a **BMO certificate** for the cofactor boundary log-modulus `Port.cofactorLogAbs ρ`, and
- the existing Fefferman–Stein axiom (already discharged into `HardyDirichletCarlesonBudget cofactorEbox_poisson`),
- plus the existing (currently axiomatized) cofactor Green/CR bound.

This file provides a drop-in replacement theorem that removes the `RGAssumptions` parameter and instead
takes the explicit cofactor BMO certificate.
-/

import RiemannRecognitionGeometry.Axioms
import RiemannRecognitionGeometry.Port.CofactorTailBound
import RiemannRecognitionGeometry.Port.CofactorCRGreenAssumptions

noncomputable section

namespace RiemannRecognitionGeometry
namespace Port

open Real Complex Set

/-- **Blaschke dominates total (Port route)**.

Same conclusion as `Axioms.blaschke_dominates_total`, but the tail bound is obtained from
`Port.weierstrass_tail_bound_cofactorEbox_poisson` (hence no `RGAssumptions` input). -/
theorem blaschke_dominates_total_of_cofactorBMO (I : WhitneyInterval) (ρ : ℂ)
    (hCA : ClassicalAnalysisAssumptions)
    (hρ_zero : completedRiemannZeta ρ = 0)
    (M : ℝ)
    (h_bmo : InBMOWithBound (cofactorLogAbs ρ) M)
    (hρ_re : 1/2 < ρ.re)
    (hρ_re_upper : ρ.re ≤ 1/2 + 2 * I.len)
    (hρ_im : ρ.im ∈ I.interval)
    (hρ_re_strict : ρ.re < 1)
    (hI_len_large : I.len ≥ 7)
    (h_centered : |ρ.im - I.t0| ≤ I.len / 2)
    (_hρ_im_ne : ρ.im ≠ 0) :
    totalPhaseSignal I ≥ L_rec - U_tail M := by
  let d := ρ.re - 1/2
  let y_hi := I.t0 + I.len - ρ.im
  let y_lo := I.t0 - I.len - ρ.im
  let blaschke_fs := Real.arctan (y_lo / d) - Real.arctan (y_hi / d)

  -- Tail bound (Port route), formulated in `Real.Angle` (phase modulo 2π)
  have h_tail :
      ‖xiPhaseChangeAngle I - (blaschke_fs : Real.Angle)‖ ≤ U_tail M := by
    -- `Port.weierstrass_tail_bound_cofactorEbox_poisson` uses the same `blaschke` expression.
    simpa [d, y_hi, y_lo, blaschke_fs] using
      (weierstrass_tail_bound_cofactorEbox_poisson
        (hCA := hCA) (I := I) (ρ := ρ) (M := M)
        (h_bmo := h_bmo) (hρ_zero := hρ_zero) (hρ_im := hρ_im))

  -- Critical line phase bound (already proven in the main RG development)
  have h_phase_ge_abs : |blaschke_fs| ≥ L_rec := by
    -- |arctan(lo) - arctan(hi)| = arctan(hi) - arctan(lo)
    rw [abs_sub_comm]
    have h_pos : Real.arctan (y_hi / d) - Real.arctan (y_lo / d) ≥ 0 := by
        have h_d_pos : d > 0 := by simp only [d]; linarith
        have h_yhi_gt_ylo : y_hi > y_lo := by
          simp only [y_hi, y_lo]
          have := I.len_pos
          linarith
        have h_div_lt : y_lo / d < y_hi / d := div_lt_div_of_pos_right h_yhi_gt_ylo h_d_pos
        have h_arctan := Real.arctan_lt_arctan h_div_lt
        linarith
    rw [_root_.abs_of_nonneg h_pos]
    exact criticalLine_phase_ge_L_rec I ρ hρ_zero hρ_im hρ_re hρ_re_upper hρ_re_strict hI_len_large h_centered

  -- Convert the Blaschke real phase to an `Angle`-norm (same lemma as in `Axioms.blaschke_dominates_total`)
  have h_abs_le_pi : |blaschke_fs| ≤ Real.pi := by
    have hA : |Real.arctan (y_lo / d)| ≤ Real.pi / 2 := by
      apply abs_le.2
      constructor
      · exact le_of_lt (Real.neg_pi_div_two_lt_arctan (y_lo / d))
      · exact le_of_lt (Real.arctan_lt_pi_div_two (y_lo / d))
    have hB : |Real.arctan (y_hi / d)| ≤ Real.pi / 2 := by
      apply abs_le.2
      constructor
      · exact le_of_lt (Real.neg_pi_div_two_lt_arctan (y_hi / d))
      · exact le_of_lt (Real.arctan_lt_pi_div_two (y_hi / d))
    have h_sub : |blaschke_fs| ≤ |Real.arctan (y_lo / d)| + |Real.arctan (y_hi / d)| := by
      simpa [blaschke_fs, sub_eq_add_neg, abs_neg] using
        (abs_add (Real.arctan (y_lo / d)) (-Real.arctan (y_hi / d)))
    have h_sum : |Real.arctan (y_lo / d)| + |Real.arctan (y_hi / d)| ≤ Real.pi := by
      nlinarith [hA, hB]
    exact le_trans h_sub h_sum

  have hp : (2 * Real.pi : ℝ) ≠ 0 := by nlinarith [Real.pi_pos]
  have h_norm_eq_abs : ‖(blaschke_fs : Real.Angle)‖ = |blaschke_fs| := by
    have h_half_period : |blaschke_fs| ≤ |(2 * Real.pi : ℝ)| / 2 := by
      have hpos : 0 < (2 * Real.pi : ℝ) := by nlinarith [Real.pi_pos]
      have hRHS : |(2 * Real.pi : ℝ)| / 2 = Real.pi := by
        calc
          |(2 * Real.pi : ℝ)| / 2 = (2 * Real.pi) / 2 := by simp [abs_of_pos hpos]
          _ = Real.pi := by
                simpa [mul_comm] using
                  (mul_div_cancel_left₀ (Real.pi) (2 : ℝ) (two_ne_zero : (2 : ℝ) ≠ 0))
      simpa [hRHS] using h_abs_le_pi
    exact (AddCircle.norm_coe_eq_abs_iff (p := (2 * Real.pi)) (x := blaschke_fs) hp).2 h_half_period

  have h_phase_ge : ‖(blaschke_fs : Real.Angle)‖ ≥ L_rec := by
    simpa [h_norm_eq_abs] using h_phase_ge_abs

  -- Reverse triangle inequality in the normed group `Real.Angle`.
  have h_rev :
      ‖(blaschke_fs : Real.Angle)‖ - ‖xiPhaseChangeAngle I - (blaschke_fs : Real.Angle)‖ ≤
        ‖xiPhaseChangeAngle I‖ := by
    have h1 :
        ‖(blaschke_fs : Real.Angle)‖ - ‖xiPhaseChangeAngle I‖ ≤
          ‖xiPhaseChangeAngle I - (blaschke_fs : Real.Angle)‖ := by
      have h0 := norm_sub_norm_le (a := (blaschke_fs : Real.Angle)) (b := xiPhaseChangeAngle I)
      simpa [norm_sub_rev] using h0
    have h2 :
        ‖(blaschke_fs : Real.Angle)‖ ≤
          ‖xiPhaseChangeAngle I - (blaschke_fs : Real.Angle)‖ + ‖xiPhaseChangeAngle I‖ :=
      (sub_le_iff_le_add).1 h1
    have h2' :
        ‖(blaschke_fs : Real.Angle)‖ ≤
          ‖xiPhaseChangeAngle I‖ + ‖xiPhaseChangeAngle I - (blaschke_fs : Real.Angle)‖ := by
      simpa [add_comm] using h2
    exact (sub_le_iff_le_add).2 h2'

  have h_rev' : ‖(blaschke_fs : Real.Angle)‖ - U_tail M ≤ ‖xiPhaseChangeAngle I‖ := by
    have h_sub :
        ‖(blaschke_fs : Real.Angle)‖ - U_tail M ≤
        ‖(blaschke_fs : Real.Angle)‖ - ‖xiPhaseChangeAngle I - (blaschke_fs : Real.Angle)‖ :=
      sub_le_sub_left h_tail ‖(blaschke_fs : Real.Angle)‖
    exact le_trans h_sub h_rev

  -- `‖xiPhaseChangeAngle I‖ = totalPhaseSignal I` by definition.
  have h_total : ‖xiPhaseChangeAngle I‖ = totalPhaseSignal I := by rfl
  have h_rev'' : ‖(blaschke_fs : Real.Angle)‖ - U_tail M ≤ totalPhaseSignal I := by
    simpa [h_total] using h_rev'

  -- Combine: ‖blaschke‖ ≥ L_rec and ‖phase‖ ≥ ‖blaschke‖ - U_tail.
  linarith

/-- Variant of `blaschke_dominates_total_of_cofactorBMO` that uses the **energy-based**
CR/Green target bundle `Port.CofactorCRGreenAssumptions` (instead of `ClassicalAnalysisAssumptions`). -/
theorem blaschke_dominates_total_of_cofactorBMO_of_cofactorCRGreenAssumptions
    (I : WhitneyInterval) (ρ : ℂ)
    (hGreen : CofactorCRGreenAssumptions)
    (hρ_zero : completedRiemannZeta ρ = 0)
    (M : ℝ)
    (h_bmo : InBMOWithBound (cofactorLogAbs ρ) M)
    (hρ_re : 1/2 < ρ.re)
    (hρ_re_upper : ρ.re ≤ 1/2 + 2 * I.len)
    (hρ_im : ρ.im ∈ I.interval)
    (hρ_re_strict : ρ.re < 1)
    (hI_len_large : I.len ≥ 7)
    (h_centered : |ρ.im - I.t0| ≤ I.len / 2)
    (_hρ_im_ne : ρ.im ≠ 0) :
    totalPhaseSignal I ≥ L_rec - U_tail M := by
  let d := ρ.re - 1/2
  let y_hi := I.t0 + I.len - ρ.im
  let y_lo := I.t0 - I.len - ρ.im
  let blaschke_fs := Real.arctan (y_lo / d) - Real.arctan (y_hi / d)

  -- Tail bound (Port route), formulated in `Real.Angle` (phase modulo 2π)
  have h_tail :
      ‖xiPhaseChangeAngle I - (blaschke_fs : Real.Angle)‖ ≤ U_tail M := by
    simpa [d, y_hi, y_lo, blaschke_fs] using
      (weierstrass_tail_bound_cofactorEbox_poisson_of_cofactorCRGreenAssumptions
        (h := hGreen) (I := I) (ρ := ρ) (M := M)
        (h_bmo := h_bmo) (hρ_zero := hρ_zero) (hρ_im := hρ_im))

  -- Critical line phase bound (already proven in the main RG development)
  have h_phase_ge_abs : |blaschke_fs| ≥ L_rec := by
    -- |arctan(lo) - arctan(hi)| = arctan(hi) - arctan(lo)
    rw [abs_sub_comm]
    have h_pos : Real.arctan (y_hi / d) - Real.arctan (y_lo / d) ≥ 0 := by
        have h_d_pos : d > 0 := by simp only [d]; linarith
        have h_yhi_gt_ylo : y_hi > y_lo := by
          simp only [y_hi, y_lo]
          have := I.len_pos
          linarith
        have h_div_lt : y_lo / d < y_hi / d := div_lt_div_of_pos_right h_yhi_gt_ylo h_d_pos
        have h_arctan := Real.arctan_lt_arctan h_div_lt
        linarith
    rw [_root_.abs_of_nonneg h_pos]
    exact criticalLine_phase_ge_L_rec I ρ hρ_zero hρ_im hρ_re hρ_re_upper hρ_re_strict hI_len_large h_centered

  -- Convert the Blaschke real phase to an `Angle`-norm (same lemma as in `Axioms.blaschke_dominates_total`)
  have h_abs_le_pi : |blaschke_fs| ≤ Real.pi := by
    have hA : |Real.arctan (y_lo / d)| ≤ Real.pi / 2 := by
      apply abs_le.2
      constructor
      · exact le_of_lt (Real.neg_pi_div_two_lt_arctan (y_lo / d))
      · exact le_of_lt (Real.arctan_lt_pi_div_two (y_lo / d))
    have hB : |Real.arctan (y_hi / d)| ≤ Real.pi / 2 := by
      apply abs_le.2
      constructor
      · exact le_of_lt (Real.neg_pi_div_two_lt_arctan (y_hi / d))
      · exact le_of_lt (Real.arctan_lt_pi_div_two (y_hi / d))
    have h_sub : |blaschke_fs| ≤ |Real.arctan (y_lo / d)| + |Real.arctan (y_hi / d)| := by
      simpa [blaschke_fs, sub_eq_add_neg, abs_neg] using
        (abs_add (Real.arctan (y_lo / d)) (-Real.arctan (y_hi / d)))
    have h_sum : |Real.arctan (y_lo / d)| + |Real.arctan (y_hi / d)| ≤ Real.pi := by
      nlinarith [hA, hB]
    exact le_trans h_sub h_sum

  have hp : (2 * Real.pi : ℝ) ≠ 0 := by nlinarith [Real.pi_pos]
  have h_norm_eq_abs : ‖(blaschke_fs : Real.Angle)‖ = |blaschke_fs| := by
    have h_half_period : |blaschke_fs| ≤ |(2 * Real.pi : ℝ)| / 2 := by
      have hpos : 0 < (2 * Real.pi : ℝ) := by nlinarith [Real.pi_pos]
      have hRHS : |(2 * Real.pi : ℝ)| / 2 = Real.pi := by
        calc
          |(2 * Real.pi : ℝ)| / 2 = (2 * Real.pi) / 2 := by simp [abs_of_pos hpos]
          _ = Real.pi := by
                simpa [mul_comm] using
                  (mul_div_cancel_left₀ (Real.pi) (2 : ℝ) (two_ne_zero : (2 : ℝ) ≠ 0))
      simpa [hRHS] using h_abs_le_pi
    exact (AddCircle.norm_coe_eq_abs_iff (p := (2 * Real.pi)) (x := blaschke_fs) hp).2 h_half_period

  have h_phase_ge : ‖(blaschke_fs : Real.Angle)‖ ≥ L_rec := by
    simpa [h_norm_eq_abs] using h_phase_ge_abs

  -- Reverse triangle inequality in the normed group `Real.Angle`.
  have h_rev :
      ‖(blaschke_fs : Real.Angle)‖ - ‖xiPhaseChangeAngle I - (blaschke_fs : Real.Angle)‖ ≤
        ‖xiPhaseChangeAngle I‖ := by
    have h1 :
        ‖(blaschke_fs : Real.Angle)‖ - ‖xiPhaseChangeAngle I‖ ≤
          ‖xiPhaseChangeAngle I - (blaschke_fs : Real.Angle)‖ := by
      have h0 := norm_sub_norm_le (a := (blaschke_fs : Real.Angle)) (b := xiPhaseChangeAngle I)
      simpa [norm_sub_rev] using h0
    have h2 :
        ‖(blaschke_fs : Real.Angle)‖ ≤
          ‖xiPhaseChangeAngle I - (blaschke_fs : Real.Angle)‖ + ‖xiPhaseChangeAngle I‖ :=
      (sub_le_iff_le_add).1 h1
    have h2' :
        ‖(blaschke_fs : Real.Angle)‖ ≤
          ‖xiPhaseChangeAngle I‖ + ‖xiPhaseChangeAngle I - (blaschke_fs : Real.Angle)‖ := by
      simpa [add_comm] using h2
    exact (sub_le_iff_le_add).2 h2'

  have h_rev' : ‖(blaschke_fs : Real.Angle)‖ - U_tail M ≤ ‖xiPhaseChangeAngle I‖ := by
    have h_sub :
        ‖(blaschke_fs : Real.Angle)‖ - U_tail M ≤
        ‖(blaschke_fs : Real.Angle)‖ - ‖xiPhaseChangeAngle I - (blaschke_fs : Real.Angle)‖ :=
      sub_le_sub_left h_tail ‖(blaschke_fs : Real.Angle)‖
    exact le_trans h_sub h_rev

  -- `‖xiPhaseChangeAngle I‖ = totalPhaseSignal I` by definition.
  have h_total : ‖xiPhaseChangeAngle I‖ = totalPhaseSignal I := by rfl
  have h_rev'' : ‖(blaschke_fs : Real.Angle)‖ - U_tail M ≤ totalPhaseSignal I := by
    simpa [h_total] using h_rev'

  -- Combine: ‖blaschke‖ ≥ L_rec and ‖phase‖ ≥ ‖blaschke‖ - U_tail.
  linarith

/-- **Centered interval choice (Port route)**.

Same conclusion as `Axioms.blaschke_dominates_total_centered`, but with the tail bound obtained from
`Port.weierstrass_tail_bound_cofactorEbox_poisson` (hence no `RGAssumptions` input). -/
theorem blaschke_dominates_total_centered_of_cofactorBMO (ρ : ℂ)
    (hCA : ClassicalAnalysisAssumptions)
    (hρ_zero : completedRiemannZeta ρ = 0)
    (M : ℝ)
    (h_bmo : InBMOWithBound (cofactorLogAbs ρ) M)
    (hρ_re : 1/2 < ρ.re) :
    let d : ℝ := ρ.re - 1/2
    let I0 : WhitneyInterval :=
      { t0 := ρ.im
        len := 2 * d
        len_pos := by
          have : d > 0 := by simp [d]; linarith
          nlinarith }
    totalPhaseSignal I0 ≥ L_rec - U_tail M := by
  intro d I0
  have h_d_pos : d > 0 := by simp only [d]; linarith
  have h_d_nonneg : 0 ≤ d := le_of_lt h_d_pos

  -- Basic facts about the centered interval
  have hρ_im0 : ρ.im ∈ I0.interval := by
    -- ρ.im ∈ [ρ.im - 2d, ρ.im + 2d] is trivially true for d ≥ 0.
    simp only [WhitneyInterval.interval, I0, Set.mem_Icc]
    constructor <;> linarith

  -- Tail bound in `Real.Angle`
  let y_hi : ℝ := I0.t0 + I0.len - ρ.im
  let y_lo : ℝ := I0.t0 - I0.len - ρ.im
  let blaschke_fs : ℝ := Real.arctan (y_lo / d) - Real.arctan (y_hi / d)
  have h_tail :
      ‖xiPhaseChangeAngle I0 - (blaschke_fs : Real.Angle)‖ ≤ U_tail M := by
    simpa [y_hi, y_lo, blaschke_fs, d] using
      (weierstrass_tail_bound_cofactorEbox_poisson
        (hCA := hCA) (I := I0) (ρ := ρ) (M := M)
        (h_bmo := h_bmo) (hρ_zero := hρ_zero) (hρ_im := hρ_im0))

  -- Compute the Blaschke real phase for the centered choice: it is `- 2 * arctan 2`.
  have h_yhi : y_hi = 2 * d := by simp only [y_hi, I0]; ring
  have h_ylo : y_lo = -(2 * d) := by simp only [y_lo, I0]; ring
  have h_blaschke :
      blaschke_fs = - (2 * Real.arctan 2) := by
    -- y_hi/d = 2 and y_lo/d = -2
    have h1 : y_hi / d = 2 := by
      rw [h_yhi]
      field_simp [h_d_pos.ne']
    have h2 : y_lo / d = -2 := by
      rw [h_ylo]
      field_simp [h_d_pos.ne']
    -- unfold blaschke_fs and rewrite arctans
    simp only [blaschke_fs, h1, h2, Real.arctan_neg]
    ring

  have h_abs_ge : |blaschke_fs| ≥ L_rec := by
    -- |blaschke_fs| = 2 * arctan 2 > 2.2 = L_rec
    have h_two_arctan_two : 2 * Real.arctan 2 > 2.2 := by
      have := arctan_two_gt_one_point_one
      linarith
    have h_abs : |blaschke_fs| = 2 * Real.arctan 2 := by
      have hpos : 0 < 2 * Real.arctan 2 := by
        have := arctan_two_gt_one_point_one
        linarith
      rw [h_blaschke, abs_neg, abs_of_pos hpos]
    rw [h_abs]
    unfold L_rec
    linarith

  -- Convert |blaschke_fs| lower bound into an `Angle`-norm lower bound.
  have h_abs_le_pi : |blaschke_fs| ≤ Real.pi := by
    -- Same bound as in `Axioms.blaschke_dominates_total_centered`: `|arctan x| ≤ π/2`.
    have hA : |Real.arctan (y_lo / d)| ≤ Real.pi / 2 := by
      apply abs_le.2
      constructor
      · exact le_of_lt (Real.neg_pi_div_two_lt_arctan (y_lo / d))
      · exact le_of_lt (Real.arctan_lt_pi_div_two (y_lo / d))
    have hB : |Real.arctan (y_hi / d)| ≤ Real.pi / 2 := by
      apply abs_le.2
      constructor
      · exact le_of_lt (Real.neg_pi_div_two_lt_arctan (y_hi / d))
      · exact le_of_lt (Real.arctan_lt_pi_div_two (y_hi / d))
    have h_sub : |blaschke_fs| ≤ |Real.arctan (y_lo / d)| + |Real.arctan (y_hi / d)| := by
      simpa [blaschke_fs, sub_eq_add_neg, abs_neg] using
        (abs_add (Real.arctan (y_lo / d)) (-Real.arctan (y_hi / d)))
    have h_sum : |Real.arctan (y_lo / d)| + |Real.arctan (y_hi / d)| ≤ Real.pi := by
      nlinarith [hA, hB]
    exact le_trans h_sub h_sum

  have hp : (2 * Real.pi : ℝ) ≠ 0 := by nlinarith [Real.pi_pos]
  have h_norm_eq_abs : ‖(blaschke_fs : Real.Angle)‖ = |blaschke_fs| := by
    have h_half_period : |blaschke_fs| ≤ |(2 * Real.pi : ℝ)| / 2 := by
      have hpos : 0 < (2 * Real.pi : ℝ) := by nlinarith [Real.pi_pos]
      have hRHS : |(2 * Real.pi : ℝ)| / 2 = Real.pi := by
        calc
          |(2 * Real.pi : ℝ)| / 2 = (2 * Real.pi) / 2 := by simp [abs_of_pos hpos]
          _ = Real.pi := by
                simpa [mul_comm] using
                  (mul_div_cancel_left₀ (Real.pi) (2 : ℝ) (two_ne_zero : (2 : ℝ) ≠ 0))
      simpa [hRHS] using h_abs_le_pi
    exact (AddCircle.norm_coe_eq_abs_iff (p := (2 * Real.pi)) (x := blaschke_fs) hp).2 h_half_period

  have h_phase_ge : ‖(blaschke_fs : Real.Angle)‖ ≥ L_rec := by
    rw [h_norm_eq_abs]
    exact h_abs_ge

  -- Reverse triangle inequality in `Real.Angle` as in the main RG proof.
  have h_rev :
      ‖(blaschke_fs : Real.Angle)‖ - ‖xiPhaseChangeAngle I0 - (blaschke_fs : Real.Angle)‖ ≤
        ‖xiPhaseChangeAngle I0‖ := by
    have h := norm_sub_norm_le (blaschke_fs : Real.Angle) (xiPhaseChangeAngle I0)
    have h' : ‖(blaschke_fs : Real.Angle) - xiPhaseChangeAngle I0‖ =
              ‖xiPhaseChangeAngle I0 - (blaschke_fs : Real.Angle)‖ := norm_sub_rev _ _
    linarith [h, h']

  have h_rev' : ‖(blaschke_fs : Real.Angle)‖ - U_tail M ≤ ‖xiPhaseChangeAngle I0‖ := by
    have h_sub : ‖(blaschke_fs : Real.Angle)‖ - U_tail M ≤
        ‖(blaschke_fs : Real.Angle)‖ - ‖xiPhaseChangeAngle I0 - (blaschke_fs : Real.Angle)‖ :=
      sub_le_sub_left h_tail ‖(blaschke_fs : Real.Angle)‖
    exact le_trans h_sub h_rev

  have h_total : ‖xiPhaseChangeAngle I0‖ = totalPhaseSignal I0 := rfl
  have h_rev'' : ‖(blaschke_fs : Real.Angle)‖ - U_tail M ≤ totalPhaseSignal I0 := by
    rw [← h_total]
    exact h_rev'

  -- Combine the lower bound on `‖blaschke_fs‖` with the reverse inequality.
  linarith

/-- Variant of `blaschke_dominates_total_centered_of_cofactorBMO` using the energy-based
CR/Green target bundle `Port.CofactorCRGreenAssumptions` (instead of `ClassicalAnalysisAssumptions`). -/
theorem blaschke_dominates_total_centered_of_cofactorBMO_of_cofactorCRGreenAssumptions (ρ : ℂ)
    (hGreen : CofactorCRGreenAssumptions)
    (hρ_zero : completedRiemannZeta ρ = 0)
    (M : ℝ)
    (h_bmo : InBMOWithBound (cofactorLogAbs ρ) M)
    (hρ_re : 1/2 < ρ.re) :
    let d : ℝ := ρ.re - 1/2
    let I0 : WhitneyInterval :=
      { t0 := ρ.im
        len := 2 * d
        len_pos := by
          have : d > 0 := by simp [d]; linarith
          nlinarith }
    totalPhaseSignal I0 ≥ L_rec - U_tail M := by
  intro d I0
  have h_d_pos : d > 0 := by simp only [d]; linarith

  -- Basic facts about the centered interval
  have hρ_im0 : ρ.im ∈ I0.interval := by
    simp only [WhitneyInterval.interval, I0, Set.mem_Icc]
    constructor <;> linarith

  -- Tail bound in `Real.Angle`
  let y_hi : ℝ := I0.t0 + I0.len - ρ.im
  let y_lo : ℝ := I0.t0 - I0.len - ρ.im
  let blaschke_fs : ℝ := Real.arctan (y_lo / d) - Real.arctan (y_hi / d)
  have h_tail :
      ‖xiPhaseChangeAngle I0 - (blaschke_fs : Real.Angle)‖ ≤ U_tail M := by
    simpa [y_hi, y_lo, blaschke_fs, d] using
      (weierstrass_tail_bound_cofactorEbox_poisson_of_cofactorCRGreenAssumptions
        (h := hGreen) (I := I0) (ρ := ρ) (M := M)
        (h_bmo := h_bmo) (hρ_zero := hρ_zero) (hρ_im := hρ_im0))

  -- Compute the Blaschke real phase for the centered choice: it is `- 2 * arctan 2`.
  have h_yhi : y_hi = 2 * d := by simp only [y_hi, I0]; ring
  have h_ylo : y_lo = -(2 * d) := by simp only [y_lo, I0]; ring
  have h_blaschke :
      blaschke_fs = - (2 * Real.arctan 2) := by
    have h1 : y_hi / d = 2 := by
      rw [h_yhi]
      field_simp [h_d_pos.ne']
    have h2 : y_lo / d = -2 := by
      rw [h_ylo]
      field_simp [h_d_pos.ne']
    simp only [blaschke_fs, h1, h2, Real.arctan_neg]
    ring

  have h_abs_ge : |blaschke_fs| ≥ L_rec := by
    have h_two_arctan_two : 2 * Real.arctan 2 > 2.2 := by
      have := arctan_two_gt_one_point_one
      linarith
    have h_abs : |blaschke_fs| = 2 * Real.arctan 2 := by
      have hpos : 0 < 2 * Real.arctan 2 := by
        have := arctan_two_gt_one_point_one
        linarith
      rw [h_blaschke, abs_neg, abs_of_pos hpos]
    rw [h_abs]
    unfold L_rec
    linarith

  -- Convert |blaschke_fs| lower bound into an `Angle`-norm lower bound.
  have h_abs_le_pi : |blaschke_fs| ≤ Real.pi := by
    have hA : |Real.arctan (y_lo / d)| ≤ Real.pi / 2 := by
      apply abs_le.2
      constructor
      · exact le_of_lt (Real.neg_pi_div_two_lt_arctan (y_lo / d))
      · exact le_of_lt (Real.arctan_lt_pi_div_two (y_lo / d))
    have hB : |Real.arctan (y_hi / d)| ≤ Real.pi / 2 := by
      apply abs_le.2
      constructor
      · exact le_of_lt (Real.neg_pi_div_two_lt_arctan (y_hi / d))
      · exact le_of_lt (Real.arctan_lt_pi_div_two (y_hi / d))
    have h_sub : |blaschke_fs| ≤ |Real.arctan (y_lo / d)| + |Real.arctan (y_hi / d)| := by
      simpa [blaschke_fs, sub_eq_add_neg, abs_neg] using
        (abs_add (Real.arctan (y_lo / d)) (-Real.arctan (y_hi / d)))
    have h_sum : |Real.arctan (y_lo / d)| + |Real.arctan (y_hi / d)| ≤ Real.pi := by
      nlinarith [hA, hB]
    exact le_trans h_sub h_sum

  have hp : (2 * Real.pi : ℝ) ≠ 0 := by nlinarith [Real.pi_pos]
  have h_norm_eq_abs : ‖(blaschke_fs : Real.Angle)‖ = |blaschke_fs| := by
    have h_half_period : |blaschke_fs| ≤ |(2 * Real.pi : ℝ)| / 2 := by
      have hpos : 0 < (2 * Real.pi : ℝ) := by nlinarith [Real.pi_pos]
      have hRHS : |(2 * Real.pi : ℝ)| / 2 = Real.pi := by
        calc
          |(2 * Real.pi : ℝ)| / 2 = (2 * Real.pi) / 2 := by simp [abs_of_pos hpos]
          _ = Real.pi := by
                simpa [mul_comm] using
                  (mul_div_cancel_left₀ (Real.pi) (2 : ℝ) (two_ne_zero : (2 : ℝ) ≠ 0))
      simpa [hRHS] using h_abs_le_pi
    exact (AddCircle.norm_coe_eq_abs_iff (p := (2 * Real.pi)) (x := blaschke_fs) hp).2 h_half_period

  have h_phase_ge : ‖(blaschke_fs : Real.Angle)‖ ≥ L_rec := by
    rw [h_norm_eq_abs]
    exact h_abs_ge

  -- Reverse triangle inequality in `Real.Angle`.
  have h_rev :
      ‖(blaschke_fs : Real.Angle)‖ - ‖xiPhaseChangeAngle I0 - (blaschke_fs : Real.Angle)‖ ≤
        ‖xiPhaseChangeAngle I0‖ := by
    have h := norm_sub_norm_le (blaschke_fs : Real.Angle) (xiPhaseChangeAngle I0)
    have h' : ‖(blaschke_fs : Real.Angle) - xiPhaseChangeAngle I0‖ =
              ‖xiPhaseChangeAngle I0 - (blaschke_fs : Real.Angle)‖ := norm_sub_rev _ _
    linarith [h, h']

  have h_rev' : ‖(blaschke_fs : Real.Angle)‖ - U_tail M ≤ ‖xiPhaseChangeAngle I0‖ := by
    have h_sub : ‖(blaschke_fs : Real.Angle)‖ - U_tail M ≤
        ‖(blaschke_fs : Real.Angle)‖ - ‖xiPhaseChangeAngle I0 - (blaschke_fs : Real.Angle)‖ :=
      sub_le_sub_left h_tail ‖(blaschke_fs : Real.Angle)‖
    exact le_trans h_sub h_rev

  have h_total : ‖xiPhaseChangeAngle I0‖ = totalPhaseSignal I0 := rfl
  have h_rev'' : ‖(blaschke_fs : Real.Angle)‖ - U_tail M ≤ totalPhaseSignal I0 := by
    rw [← h_total]
    exact h_rev'

  linarith

end Port
end RiemannRecognitionGeometry
