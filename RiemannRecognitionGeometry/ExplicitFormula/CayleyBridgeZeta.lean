/-!
# Deprecated: Cayley bridge ζ scaffold

This file previously contained a standalone Cayley-bridge scaffold with local axioms
(`positivity_hypothesis_zeta`, `spectral_bridge_hypothesis`, etc.).

It is now **deprecated** in favor of the canonical entrypoints:

- `RiemannRecognitionGeometry/ExplicitFormula/ZetaInstantiation.lean`
  (ζ PSC-components and the single Cayley measure-bridge assumption surface)
- `RiemannRecognitionGeometry/ExplicitFormula/ZetaEndToEndSchwartz.lean`
  (right-edge assumptions → Route 3 → `RiemannHypothesis`)
- `RiemannRecognitionGeometry/ExplicitFormula/PSCSplice.lean`
  (measure-first splice identity → Route 3 → `RiemannHypothesis`)

We keep only lightweight re-exports here to avoid duplicating (and diverging) axiom surfaces.
-/

import RiemannRecognitionGeometry.ExplicitFormula.ZetaInstantiation
import RiemannRecognitionGeometry.ExplicitFormula.ZetaEndToEndSchwartz

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula
namespace CayleyBridgeZeta

open ZetaInstantiation

/-- Re-export: RH from the ζ Cayley measure-bridge assumptions (see `ZetaInstantiation`). -/
abbrev RH_of_cayleyBridge_zeta
    (L : LagariasFramework Route3.F)
    (Aμ : Route3.PSCSplice.Assumptions) :
    RiemannHypothesis :=
  ZetaInstantiation.RH_of_cayleyBridge_zeta (L := L) (Aμ := Aμ)

/-- Re-export: end-to-end “right-edge → splice → RH” theorem (see `ZetaEndToEndSchwartz`). -/
abbrev RH_of_endToEnd (A : ZetaInstantiation.EndToEnd.Assumptions) : RiemannHypothesis :=
  ZetaInstantiation.EndToEnd.RH (A := A)

/-- Re-export: end-to-end “boundary wedge + splice identity → RH” theorem (see `ZetaEndToEndSchwartz`). -/
abbrev RH_of_splice (A : ZetaInstantiation.EndToEnd.AssumptionsSplice) : RiemannHypothesis :=
  ZetaInstantiation.EndToEnd.RH_of_splice (A := A)

end CayleyBridgeZeta
end ExplicitFormula
end RiemannRecognitionGeometry
