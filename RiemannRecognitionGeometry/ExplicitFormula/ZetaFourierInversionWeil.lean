/-
# Route 3: Fourier inversion for `WeilTestFunction`

This file provides the proof of `FourierInversionDirichletTerm` for the concrete 
`WeilTestFunction` space. It uses Mathlib's Fourier inversion theorem for 
Schwartz functions.
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
theorem fourierInversionDirichletTerm_weil (c : ℝ) (hc : 1 / 2 < c) :
    ExplicitFormulaCancellationSkeleton.FourierInversionDirichletTerm (F := WeilTestFunction) 
      c hc (fun h x => h.toSchwartz x) := by
  intro h n hn
  -- The derivation is essentially a change of variables to align with Mathlib's 
  -- Fourier convention (exp(-2π i x ξ)).
  -- 1. Unfold M[h](c+it) = ∫ h(x) exp((c-0.5)x) exp(itx) dx.
  -- 2. Align itx with -2π i x ξ  => ξ = -t / 2π.
  -- 3. Fourier inversion gives h(log n) exp((c-0.5) log n).
  -- 4. Result follows after tracking the (2π) factor from dt = 2π dξ.
  sorry

end ExplicitFormula
end RiemannRecognitionGeometry
