# Proof route strawman (Dec 2025)

Goal: choose **one primary route** to push toward an *unconditional* proof, while preserving “parking lot” notes for the other routes so we don’t lose context.

This is intentionally a **strawman**: it’s meant to be updated as soon as we learn something that changes the ROI/risk.

---

## Decision summary (current recommendation)

**Primary route to pursue:** **Route‑3′ (Connes / determinant approximants → Hurwitz)**

**Why this is the best bet (strawman):**
- It cleanly isolates the “new math” into a **small number of typed targets** (M1/M2 in `ExplicitFormula/ConnesConvergenceBundle.lean`).
- Everything after convergence is **standard complex analysis** (Hurwitz nonvanishing + zero correspondence glue).
- The Lean skeleton is already end-to-end: `ConnesConvergenceBundle → HurwitzGate → RH` (modulo a small number of remaining axioms).

**What this route still requires for an unconditional proof:**
- Prove the Connes missing steps:
  - **M1**: `ConnesMissingStepSimpleEven`
  - **M2**: `ConnesMissingStep_kLam_approximates_xiLam`
- Replace the remaining “standard-analysis” axioms in the Hurwitz+glue layer (we can do these anytime).

---

## What “unconditional” means in our codebase

We currently treat “unknown” steps as **explicit `axiom`s** (or, for CCM “missing steps”, as **structured Prop targets**). A route is “unconditional” when the final RH theorem depends only on Mathlib (and proven lemmas in this repo), with **no project-level `axiom`s** remaining in the dependency chain.

---

## Route‑3′ (Connes): status + next steps

**Core pipeline files**
- `RiemannRecognitionGeometry/ExplicitFormula/ConnesConvergenceBundle.lean`
- `RiemannRecognitionGeometry/ExplicitFormula/HurwitzGate.lean`
- `RiemannRecognitionGeometry/ExplicitFormula/ConnesHurwitzBridge.lean`
- Notes / translation: `notes/papers/2511.22755-zeta-spectral-triples-notes.md`

**What’s already in good shape**
- The convergence/Hurwitz “wiring” is correct and minimal.
- Nontriviality of `Ξ` on upper/lower strip is now proven (no longer axiomatized).

**Hard math targets (RH-level)**
- Prove M1/M2 as stated, ideally by directly formalizing CCM Section 7–8 with a concrete construction of the approximants.

**Standard-analysis tasks (doable, but can be postponed)**
- Prove the Hurwitz nonvanishing lemma currently axiomatized in `HurwitzGate.lean`.
- ✅ **Done**: the “Ξ zero-free off-real-axis in strip ⇒ Mathlib RH” glue is now a theorem in `ConnesHurwitzBridge.lean` (no longer an axiom).

---

## Parking lot: Route‑3 (explicit formula / reflection positivity / Cayley–Schur)

**Status:** excellent Lean wiring, but the remaining step is essentially the RH-equivalent “Weil gate / positivity kernel” bottleneck.

**High-signal docs**
- `archive/route3_docs/ROUTE3_STATUS_AND_STRATEGY.md`

**Key Lean touchpoints**
- Route‑3 main skeleton: `RiemannRecognitionGeometry/ExplicitFormula/Route3HypBundle.lean`
- Hilbert realization: `RiemannRecognitionGeometry/ExplicitFormula/HilbertRealization.lean`
- Operator/spectral-measure “drop-in”: `RiemannRecognitionGeometry/ExplicitFormula/OperatorSpectralMeasureBridge.lean`

**Why parked**
- Even with the new spectral-measure drop-in, the missing content is “prove the right boundary/spectral measure identity for ζ”, which is plausibly RH-equivalent.

---

## Parking lot: RG (μ‑Carleson / B2′ / renormalized tail)

**Status:** the contradiction driver is structurally correct; the remaining work is (i) heavy harmonic analysis infrastructure and (ii) number-theory-to-μ-Carleson translation which is RH-level.

**High-signal doc**
- `B2_LONG_TERM_STRATEGY.md`

**Key Lean touchpoints**
- Renormalized B2′ target: `RiemannRecognitionGeometry/OscillationTargetTail.lean`
- μ‑Carleson ⇒ tail decay scaffold: `RiemannRecognitionGeometry/MuCarlesonToTailDecay.lean`

**Why parked**
- Even after proving the standard harmonic analysis theorems, the remaining “μ‑Carleson from ζ zero data” step is extremely deep and diffuse.


