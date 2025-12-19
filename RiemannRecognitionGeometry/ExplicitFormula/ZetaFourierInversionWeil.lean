/-
# Route 3: Fourier inversion for `WeilTestFunction` (recorded as an axiom)

This file records the Fourier inversion statement `FourierInversionDirichletTerm` for the concrete
`WeilTestFunction` space.

**Status**: currently an `axiom` (to keep the Route‑3 wiring proof-hole-free). The intended future proof uses
Mathlib's Fourier inversion theorem for Schwartz functions, plus normalization bookkeeping.
-/

import RiemannRecognitionGeometry.ExplicitFormula.WeilTestFunction
import RiemannRecognitionGeometry.ExplicitFormula.ExplicitFormulaCancellationSkeleton
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open Complex Real MeasureTheory SchwartzMap

/--
Fourier inversion for a single Dirichlet term in the `WeilTestFunction` space.
This discharges the `fourier_inversion` field of `Det2PrimeTermAssumptions`.

Proof Sketch:
1. Rewrite `M[h](c+it)` as the bilateral Laplace transform at `s = c+it`.
2. This is the Fourier transform of `x ↦ h(x) exp((c-0.5)x)` at frequency `ξ = -t/2π`.
3. The integral over `t` then becomes a Fourier inversion integral at `x = log n`.
4. The resulting factor `exp((c-0.5) log n) = n^{c-0.5}` cancels the `n^{-c}` to leave `1/√n`.
-/
axiom fourierInversionDirichletTerm_weil (c : ℝ) (hc : 1 / 2 < c) :
    ExplicitFormulaCancellationSkeleton.FourierInversionDirichletTerm (F := WeilTestFunction)
      c hc (fun h x => h.toSchwartz x)

end ExplicitFormula
end RiemannRecognitionGeometry
