# Route 3 Mining Notes: `jonwashburn/riemann` (local: `riemann-main`)

This note records **already-formalized** components in your other RH repositories that can likely
be ported/adapted to discharge Route‑3 “hard analysis” blockers in `riemann-geometry-rs`.

## Local repo + history

- **Repo**: `github.com/jonwashburn/riemann`
- **Local clone**: `/Users/jonathanwashburn/Projects/riemann-main`
- **History**: full (`git rev-parse --is-shallow-repository` = `false`)

## High-value matches to Route‑3 blockers

### 1) Vertical/rectangle contour calculus (right-edge + horizontal vanishing pattern)

**Where (riemann-main):**
- `PrimeNumberTheoremAnd/PerronFormula.lean`
  - Key lemma: `RectangleIntegral_tendsTo_VerticalIntegral` (and variants).
  - Also: `RectangleIntegral_tendsTo_UpperU`, `RectangleIntegral_tendsTo_LowerU`

**Why it helps (Route‑3 mapping):**
- Route‑3’s `RightEdgePhaseLimitAssumptions.horizBottom_vanish` / `horizTop_vanish` and the
  right-edge truncation limits are the *same analytic shape* as “horizontal edges vanish ⇒
  rectangle integral tends to vertical integral difference”.
- Even if the contour primitives differ (`ContourW1.*` vs `RectangleIntegral`), the proof strategy
  and many of the limit lemmas are directly reusable.

---

### 2) Mellin inversion machinery (a replacement for the current Fourier-inversion sorrys)

**Where (riemann-main):**
- `PrimeNumberTheoremAnd/MediumPNT.lean`
  - Uses Mathlib’s `mellin_inversion` to evaluate a vertical-line integral into point evaluation.
  - See the block using `mellin_inversion` around the proof of `SmoothedChebyshevDirichlet`.
  - Related lemmas that make the “swap sum/integral + integrability” story work:
    - `LogDerivativeDirichlet`
    - `SmoothedChebyshevDirichlet_aux_integrable`
    - `SmoothedChebyshevDirichlet_aux_tsum_integral`
    - `SmoothedChebyshevDirichlet`

**Why it helps (Route‑3 mapping):**
- In `riemann-geometry-rs`, `ZetaFourierInversionWeil.lean` currently tries to prove
  `FourierInversionDirichletTerm` via Fourier transform normalization and has 2 `sorry`s.
- The `MediumPNT` approach shows the same “Dirichlet term inversion” can be proven via
  **Mellin inversion on `(0,∞)`** (plus standard regularity hypotheses).
- This suggests a practical refactor option: re-prove the Route‑3 Dirichlet-term identity using a
  Mellin inversion lemma (potentially after rewriting the Route‑3 `WeilTestFunction.weilTransform`
  as a Mellin transform of a function on `(0,∞)` via `x = log y`).

Concrete change-of-variables idea (the key bridge):
- Define \(f(y) := h(\log y)\,y^{-1/2}\) on \(y>0\). Then
  \[
    \mathcal M[f](s) = \int_0^\infty f(y)\,y^{s-1}\,dy
    = \int_{-\infty}^{\infty} h(x)\,e^{(s-1/2)x}\,dx
    = \texttt{weilTransform}\;h\;s.
  \]
- Mellin inversion then gives the desired “\(2\pi/\sqrt n\)” evaluation after setting \(y=n\).

Related supporting infrastructure:
- `PrimeNumberTheoremAnd/MellinCalculus.lean` (integration-by-parts, support lemmas, Haar-change-of-vars)

---

### 3) Schur / Cayley / removable singularity pinch globalization (positivity side)

**Where (riemann-main):**
- `Riemann/RS/Cayley.lean`
  - Cayley transform: `Re(F) ≥ 0` on a set ⇒ Schur bound for `(F-1)/(F+1)`.
- `Riemann/RS/SchurGlobalization.lean`
  - “Pinch” globalization across removable singularities (maximum modulus / constant function
    from `|Θ|≤1` and `Θ(ρ)=1` style).
- `Riemann/RS/OffZerosBridge.lean`
  - Non-circular packaging for off-zeros Schur decomposition + removable-extension “assignment”
    interface.

**Why it helps (Route‑3 mapping):**
- Route‑3’s `ExplicitFormula/CayleyBridge.lean` explicitly states the true bottleneck as a “bridge”
  from `Re(2·J) ≥ 0` to a positivity realization (`SesqMeasureIdentity` / reflection positivity).
- The RS repo already contains a working, sorry-free **Cayley + Schur + removable singularity**
  pipeline that is the right shape to support a positivity gate once the analytic identity linking
  the quadratic form to boundary data is in place.

---

### 4) Outer normalization and boundary unimodularity (phase bookkeeping)

**Where (riemann-main):**
- `Riemann/RS/Det2Outer.lean`
  - `BoundaryModulusEq`, `OuterHalfPlane`, `det2_nonzero_on_critical_line`
  - a concrete boundary parametrization `boundary t := 1/2 + i t` + continuity/measurability lemmas
  - simple outer witness and boundary modulus facts:
    - `O_witness`, `O_witness_boundary_abs`
- `Riemann/RS/CRGreenOuter.lean`
  - `J_CR_boundary_abs_one_ae`: derives `|J(boundary t)| = 1` a.e. from an outer modulus identity.
  - `boundary_CR_trace_bottom_edge`: packages the “identify boundary integrand with −W′ a.e.”

**Why it helps (Route‑3 mapping):**
- Route‑3 Track‑C currently has multiple ζ “boundary phase” sorries that are ultimately about the
  same bookkeeping: picking an outer factor so the ratio has unit modulus on the critical line and
  the phase is well-defined/differentiable a.e.

---

### 5) Poisson ↔ Cayley transport scaffolding (disk ↔ half-plane)

**Where (riemann-finish):**
- `riemann-finish/riemann-extra/no-zeros/rh/academic_framework/PoissonCayley.lean`
  - Defines `HasHalfPlanePoissonReEqOn`, `reEq_on_from_disk_via_cayley`,
    kernel-transport helper statements.

**Why it helps (Route‑3 mapping):**
- Your Route‑3 `CayleyMeasureBridgeAssumptions` wants a “measure-first” spectral identity.
  The Poisson/Cayley transport files are a ready-made scaffold for pushing disk Poisson identities
  into half-plane identities (the precise move needed in several RH pipelines).

## Suggested port order (highest ROI)

1. **Use `MediumPNT`’s Mellin inversion pattern** to kill the 2 `sorry`s in
   `RiemannRecognitionGeometry/ExplicitFormula/ZetaFourierInversionWeil.lean`
   (either directly or by refactoring the target lemma away from Fourier normalization).
2. **Port `RectangleIntegral_tendsTo_VerticalIntegral`-style limit algebra** to reduce the
   right-edge/horizontal-vanishing “limit” boilerplate.
3. Pull in **Schur globalization + removable singularity pinch** infrastructure if/when we move the
   Route‑3 positivity bridge from “bundle field” to actual theorems.

## Additional “bounds” library worth mining (for right-edge/horizontal limits)

**Where (riemann-main):**
- `PrimeNumberTheoremAnd/ZetaBounds.lean`

**Why it helps (Route‑3 mapping):**
- Contains a large collection of analytic estimates and holomorphic/meromorphic infrastructure
  around `riemannZeta`, `deriv riemannZeta`, residues, and rectangle integrals; likely reusable for
  proving vanishing of horizontal edges and controlling `logDeriv` terms in Route‑3 right-edge limits.


