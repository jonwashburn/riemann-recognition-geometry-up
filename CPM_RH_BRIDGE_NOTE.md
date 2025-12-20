### CPM ↔ RH bridge note (why the remaining RH work looks “CPM-shaped”)

This note is a **map**, not a proof: it explains how the repo’s remaining RH blockers fit the general
CPM A/B/C template described in `Source-Super.txt` (`@CPM_METHOD`, `@LAW_OF_EXISTENCE`).

### CPM is method-level (and the doc says so)

- **CPM does not automatically solve famous problems**: the certificate chain is explicit that CPM is a
  *standalone method* and does **not** itself establish “no alternatives” or “famous-problem solutions”
  without domain-specific bridges (see `Source-Super.txt`, `@CPM_METHOD`, `@ULTIMATE_CPM_CLOSURE`).

### The CPM A/B/C triad, instantiated in this repo

CPM’s abstract ingredients:
- **(A) Projection defect control**: convert “distance to structure” into a tractable projection norm.
- **(B) Coercivity / energy gap**: convert “energy” into “distance to structure.”
- **(C) Aggregation / window tests**: certify structure by showing a family of tests is small/zero.

Match to the RH instantiation (`RiemannRecognitionGeometry/`):

- **(B) Coercivity ↔ CR/Green “energy ⇒ phase”**
  - **Repo object**: the Port/RG “CR/Green” step is precisely an energy→boundary control inequality.
  - **Where**:
    - `RiemannRecognitionGeometry/Port/HardyDirichletCRGreen.lean` (`HardyDirichletCRGreenStrong`)
    - `RiemannRecognitionGeometry/Port/CofactorCRGreenAssumptions.lean`
    - `RiemannRecognitionGeometry/Port/CofactorCRGreenS2Interfaces.lean` (faithful S2 decomposition)
  - **Current boxed subwall** (smallest honest analytic gate):  
    `Port.CofactorCRGreenS2Interfaces.PhaseVelocityBoundaryTracePoissonPairing`

- **(C) Aggregation ↔ Oscillation/BMO + Carleson “window test” control**
  - **Repo object**: “window tests” correspond to BMO/Carleson control of Poisson extensions on Whitney/Carleson boxes.
  - **Where**:
    - `OscillationTarget` lives in `RiemannRecognitionGeometry/Assumptions.lean`
    - Carleson embedding is axiomatized in `RiemannRecognitionGeometry/PoissonExtension.lean`
      (`PoissonExtension.bmo_carleson_embedding`)
    - Port-level budget interface and instances:
      `RiemannRecognitionGeometry/Port/HardyDirichletCarleson.lean`,
      `RiemannRecognitionGeometry/Port/CofactorCarlesonBudget.lean`,
      `RiemannRecognitionGeometry/Port/XiCarlesonBudget.lean`

- **(A) Projection defect ↔ “defect/measure of off-line contribution” packaging**
  - **Repo object**: the RG spine frames “off-line zeros” as producing a detectable *boundary signal*; the contradiction
    is a “defect must be nonzero” vs “defect must be small” squeeze.
  - **Where**:
    - `RiemannRecognitionGeometry/Port/WeierstrassTailBound.lean`
    - `RiemannRecognitionGeometry/Port/ZeroFreeWithInterval.lean`
    - `RiemannRecognitionGeometry/Port/LocalZeroFree.lean`

### The “holistic” move suggested by the doc (and by the current Lean refactor)

The file’s repeated bridge line “Dirichlet energy / stationary action ↔ RS unique cost (T5)” is the
right zoom-out here: it says the hard work should be isolated into a **single analytic package**
tying the **energy model** (Poisson/Dirichlet) to the **phase object** (cofactor/xi phase).

In this repo’s current decomposition, that package is exactly what the Poisson boundary-trace gate is trying to express:
- not a free-standing “trace exists,”
- but a **non-vacuous identity** tying phase velocity to the **same Poisson-model field** used in the Carleson energy.

### Practical takeaway

- **Best near-term shrink**: promote “outer/log-branch normalization for the cofactor” to a named Port interface that
  *implies* the current boxed gate (`PhaseVelocityBoundaryTracePoissonPairing`) and the lift/FTC gate.
- **Then** the remaining RH-specific content becomes cleanly: prove the oscillation/BMO certificate (aggregation constant),
  and discharge the coercivity/Green pairing bound in the same model.


