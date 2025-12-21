/-
# Geometric tail lemmas (Route‑A / tail-sum scaffolding)

This module packages small reusable inequalities about geometric tails, used in the Route‑A
annulus decomposition and constant chasing.

It reuses the already-proved `FeffermanStein.far_field_geometric_bound` and lifts it to
constant multiples.
-/

import RiemannRecognitionGeometry.FeffermanStein
import Mathlib.Topology.Basic

noncomputable section

namespace RiemannRecognitionGeometry

open Real

/-! ## Constant-multiple geometric tail -/

/-- Lift `far_field_geometric_bound` to a constant multiple:

\[ \sum_{j>K} c·2^{-j} \le c·2^{-K}. \]

This is purely a “constant factor” convenience lemma used when summing tail contributions that
have already been reduced to geometric weights. -/
lemma far_field_geometric_bound_mul (K : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    ∑' (j : ℕ), (if j > K then c * (1/2 : ℝ)^j else 0) ≤ c * (1/2 : ℝ)^K := by
  -- factor out `c`
  have hfactor :
      (fun j : ℕ => if j > K then c * (1/2 : ℝ)^j else 0) =
        fun j : ℕ => c * (if j > K then (1/2 : ℝ)^j else 0) := by
    funext j
    by_cases hj : j > K
    · simp [hj, mul_assoc]
    · simp [hj]
  -- base geometric tail bound
  have hbase : (∑' (j : ℕ), (if j > K then (1/2 : ℝ)^j else 0)) ≤ (1/2 : ℝ)^K :=
    far_field_geometric_bound K
  -- rewrite the LHS as `c * tsum(...)`
  have htsum :
      (∑' (j : ℕ), (if j > K then c * (1/2 : ℝ)^j else 0)) =
        c * (∑' (j : ℕ), (if j > K then (1/2 : ℝ)^j else 0)) := by
    -- first rewrite the integrand into the shape `c * (...)`
    have h1 :
        (∑' (j : ℕ), (if j > K then c * (1/2 : ℝ)^j else 0)) =
          (∑' (j : ℕ), c * (if j > K then (1/2 : ℝ)^j else 0)) := by
      simp [hfactor]
    -- then pull out the constant `c`
    have h2 :
        (∑' (j : ℕ), c * (if j > K then (1/2 : ℝ)^j else 0)) =
          c * (∑' (j : ℕ), (if j > K then (1/2 : ℝ)^j else 0)) := by
      -- `tsum_mul_left` (all arguments implicit) specialized by type annotation
      simpa using
        (tsum_mul_left :
          (∑' (j : ℕ), c * (if j > K then (1/2 : ℝ)^j else 0)) =
            c * (∑' (j : ℕ), (if j > K then (1/2 : ℝ)^j else 0)))
    exact h1.trans h2
  -- multiply the base bound by `c ≥ 0`
  have hmul :
      c * (∑' (j : ℕ), (if j > K then (1/2 : ℝ)^j else 0)) ≤ c * (1/2 : ℝ)^K :=
    mul_le_mul_of_nonneg_left hbase hc
  -- avoid `simp` rewriting quirks: use a `calc` chain
  calc
    (∑' (j : ℕ), (if j > K then c * (1/2 : ℝ)^j else 0))
        = c * (∑' (j : ℕ), (if j > K then (1/2 : ℝ)^j else 0)) := htsum
    _ ≤ c * (1/2 : ℝ)^K := hmul

/-- Constant-chase helper: for any `ε > 0` and `c ≥ 0` there exists a cutoff `K` such that
`c * (1/2)^K ≤ ε`.

This is the Lean analogue of “choose K large enough so the geometric tail is below the target
constant” in the B2′ engineering step. -/
lemma exists_pow_half_mul_le {ε c : ℝ} (hε : 0 < ε) (hc : 0 ≤ c) :
    ∃ K : ℕ, c * (1/2 : ℝ)^K ≤ ε := by
  by_cases hc0 : c = 0
  · refine ⟨0, ?_⟩
    simp [hc0, hε.le]
  have hc_pos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
  -- it suffices to make `c*(1/2)^K < ε`
  have htend :
      Filter.Tendsto (fun K : ℕ => c * (1/2 : ℝ)^K) Filter.atTop (nhds 0) := by
    -- `(1/2)^K → 0`, then multiply by constant `c`
    have hpow :
        Filter.Tendsto (fun K : ℕ => (1/2 : ℝ)^K) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ (1/2 : ℝ)) (by norm_num : (1/2 : ℝ) < 1)
    simpa [mul_comm, mul_assoc] using hpow.const_mul c
  have h_event : ∀ᶠ K : ℕ in Filter.atTop, c * (1/2 : ℝ)^K < ε :=
    htend.eventually (eventually_lt_nhds hε)
  rcases (Filter.eventually_atTop.1 h_event) with ⟨K, hK⟩
  refine ⟨K, (le_of_lt (hK K le_rfl))⟩

end RiemannRecognitionGeometry
