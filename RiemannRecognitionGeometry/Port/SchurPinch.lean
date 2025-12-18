/-!
# Port alignment: Schur pinch route (already present via Route 3 infrastructure)

The `reality` blueprint contains a disabled module:
`IndisputableMonolith/RH/HardyDirichlet/SchurPinch.lean.disabled`
implementing the Schur pinch closure argument.

In this repo, the analogous Schur pinch / Schur globalization infrastructure is already
ported from `riemann-finish` under:

- `RiemannRecognitionGeometry/ExplicitFormula/OuterSchurBridge.lean`
- `RiemannRecognitionGeometry/ExplicitFormula/OuterConstruction.lean`
- `RiemannRecognitionGeometry/ExplicitFormula/CayleyBridge*.lean`

This file simply re-exports the key “pinch certificate” interface and the core
“no offcritical zeros” theorem, so the port plan can point to a stable `Port/*` path.
-/

import RiemannRecognitionGeometry.ExplicitFormula.OuterSchurBridge

noncomputable section

namespace RiemannRecognitionGeometry
namespace Port

namespace SchurPinch

open RiemannRecognitionGeometry.ExplicitFormula

/-- Re-export of the Route 3 Schur pinch certificate interface. -/
abbrev PinchCertificate (ξ : ℂ → ℂ) :=
  ExplicitFormula.OuterSchur.PinchCertificate ξ

/-- Re-export: “no offcritical zeros” from a pinch certificate (Route 3 Schur globalization). -/
theorem no_offcritical_zeros_from_certificate {ξ : ℂ → ℂ} (C : PinchCertificate ξ) :
    ∀ ρ ∈ ExplicitFormula.OuterSchur.Ω, ξ ρ ≠ 0 :=
  ExplicitFormula.OuterSchur.no_offcritical_zeros_from_certificate (C := C)

end SchurPinch

end Port
end RiemannRecognitionGeometry


