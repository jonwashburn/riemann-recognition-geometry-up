/-
# Port driver (renormalized): centered contradiction driven by `OscillationTargetTail`

This file is the structural “driver refactor” promised in `B2_LONG_TERM_STRATEGY.md`.

It provides a Port-style contradiction theorem analogous to
`RiemannRecognitionGeometry/Port/ZeroFreeWithInterval.lean`, but it consumes the **B2′**
interface `OscillationTargetTail` rather than the deprecated global `OscillationTarget`.

At this stage the two crucial analytic steps are carried as axiom stubs in
`RiemannRecognitionGeometry/OscillationTargetTail.lean`:
- an upper bound on the tail/cofactor phase signal from the local BMO certificate (D1),
- and a centered Blaschke trigger lower bound for that phase signal (D2).

This keeps Lean structurally aligned with the corrected paper proof even before the core math is done.
-/

import RiemannRecognitionGeometry.OscillationTargetTail

noncomputable section

namespace RiemannRecognitionGeometry
namespace Port

open Real Complex

/-- **Centered contradiction from B2′ (structural).**

If `ρ` were an off-critical zero, B2′ supplies a local tail BMO certificate; the driver then:
- bounds the renormalized cofactor phase from above (D1),
- bounds it from below via the centered Blaschke trigger (D2),
- and closes by the numeric inequality `U_tail(C_tail) < L_rec`.

This is the renormalized analog of `Port.zero_free_with_interval_of_OscillationTarget`. -/
theorem zero_free_with_interval_of_OscillationTargetTail (ρ : ℂ)
    (hCA : ClassicalAnalysisAssumptions)
    (hρ_re : 1/2 < ρ.re)
    (hρ_zero : completedRiemannZeta ρ = 0)
    (hT : OscillationTargetTail) :
    False := by
  -- Unpack the fixed cutoff `K` and the local BMO certificate on the centered interval.
  rcases hT with ⟨K, hK⟩

  -- Centered Whitney interval associated to `ρ`.
  set d : ℝ := ρ.re - 1/2 with hd
  have hd_pos : 0 < d := by simpa [hd] using (sub_pos.2 hρ_re)
  let I0 : WhitneyInterval :=
    { t0 := ρ.im
      len := 2 * d
      len_pos := by nlinarith [hd_pos] }

  have hBMO : InBMOWithBoundOnWhitney (tailLogAbs I0 ρ K) I0 C_tail :=
    hK ρ I0

  -- Upper bound (D1).
  have h_upper : tailPhaseSignal I0 ρ K ≤ U_tail C_tail :=
    tailPhaseSignal_bound (hCA := hCA) (I := I0) (ρ := ρ) (K := K) hBMO

  -- Lower bound (D2) for the centered choice.
  have h_lower : L_rec - U_tail C_tail ≤ tailPhaseSignal I0 ρ K := by
    simpa [hd, I0] using (tailPhaseSignal_lower_bound_centered (ρ := ρ) hρ_zero hρ_re K)

  -- Contradiction.
  -- From the squeeze:
  --   L_rec - U_tail(C_tail) ≤ tailPhaseSignal ≤ U_tail(C_tail)
  -- we get L_rec ≤ 2*U_tail(C_tail), contradicting `zero_free_condition_C_tail`.
  have h_le : L_rec - U_tail C_tail ≤ U_tail C_tail := le_trans h_lower h_upper
  have h_contra : ¬ (L_rec ≤ 2 * U_tail C_tail) := by
    have h : (2 * U_tail C_tail) < L_rec := zero_free_condition_C_tail
    exact not_le_of_lt h
  have : L_rec ≤ 2 * U_tail C_tail := by
    nlinarith [h_le]
  exact h_contra this

end Port
end RiemannRecognitionGeometry
