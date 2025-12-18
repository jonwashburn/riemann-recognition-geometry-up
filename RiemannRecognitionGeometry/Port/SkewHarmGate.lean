/-
# Port scaffold: boundary-term gate ("skew/harm tail") pattern

This file records a small, reusable analytic pattern that appears in the `reality` repo:

`/Users/jonathanwashburn/Projects/reality/IndisputableMonolith/NavierStokes/SkewHarmGate.lean`.

The core idea is:

- many “Green / integration-by-parts” arguments reduce to an identity on `(a,∞)` with a boundary term,
- and the only remaining analytic obligation is to show that boundary term tends to `0` at `∞`.

Mathlib already provides a convenient lemma for this:
if a function and its derivative are integrable on `(a,∞)`, then the function tends to `0` at `∞`.

We expose a thin wrapper with a name that matches the intended use (“gate”) so downstream RH modules
can depend on a stable interface, independent of the surrounding PDE context.
-/

import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Basic

noncomputable section

namespace RiemannRecognitionGeometry
namespace Port

open scoped Topology
open Filter MeasureTheory Set

/-- **Boundary-term gate**: if `f` is differentiable on `(a,∞)` with derivative `f'`,
and both `f` and `f'` are integrable on `(a,∞)`, then `f(x) → 0` as `x → ∞`.

This is the exact Lean form of the informal step “integrability forces the boundary term at infinity
to vanish”, used to close CR/Green arguments without carrying around explicit limit computations. -/
lemma tendsto_zero_atTop_of_hasDerivAt_of_integrableOn_Ioi
    {a : ℝ} {f f' : ℝ → ℝ}
    (hderiv : ∀ x ∈ Set.Ioi a, HasDerivAt f (f' x) x)
    (hf' : IntegrableOn f' (Set.Ioi a) volume)
    (hf : IntegrableOn f (Set.Ioi a) volume) :
    Filter.Tendsto f Filter.atTop (𝓝 (0 : ℝ)) := by
  -- Delegate to Mathlib.
  simpa using
    MeasureTheory.tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := a)
      (f := f) (f' := f') hderiv hf' hf

end Port
end RiemannRecognitionGeometry
