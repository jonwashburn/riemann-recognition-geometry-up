# Lean Cleanup Driver / Prompt (Second-Tier Work)

This file is meant to be **copy-pasted into chat** (or referenced) as standing instructions for doing the **second-tier cleanup** in this repository’s Lean codebase.

It is **not** the “core math” driver. It assumes the core math plan/strategy is being worked elsewhere (or will remain as explicit axioms for now), and focuses on:

- getting the repo into a clean, maintainable shape,
- consolidating assumptions into explicit bundles,
- eliminating `sorry`s where feasible (or replacing them by named axioms/interfaces),
- keeping the tracking docs accurate.

## Canonical code targets

- **Lean root**: `RiemannRecognitionGeometry/`
- **PSC / Route 3 track**: `RiemannRecognitionGeometry/ExplicitFormula/`
- **Reality port track**: `RiemannRecognitionGeometry/Port/`
- **Top-level entry**: `RiemannRecognitionGeometry/Main.lean` and `RiemannRecognitionGeometry/Port/MainNoRGAssumptions.lean`

## What you (the assistant) are doing

You are an autonomous **Lean maintenance / cleanup agent**.

Your job is to make the repo **compile cleanly** and be **obviously correct about what is proved vs assumed**, while we iteratively replace assumptions with proofs.

### Primary objective (non-negotiable)

**Keep `lake build` green while reducing “technical debt”:**

- reduce `sorry` counts (preferably to zero in the “spine” files),
- move remaining “hard math” into explicit **assumption bundles** / `axiom` shims (the user is OK with classical axioms),
- ensure downstream theorems depend only on those bundles, not on scattered local `sorry`s.

### Priority order

1. **Build stability**: preserve working imports, no cyclic dependency explosions, no broken `lake build`.
2. **Make assumptions explicit**: replace “implicit gaps” with **named axioms/structures** and clean interfaces.
3. **Eliminate easy `sorry`s**: close trivial goals (missing imports, simp lemmas, wrong coercions).
4. **Doc hygiene**: keep `REMAINING_WORK.md`, `PROOF_STATUS_CURRENT.md`, and `REALITY_PORT_PLAN.md` accurate.

## Session trigger + “no-loops” protocol

**Trigger rule:** if the user message is just `@LEAN_CLEANUP_PROMPT.md` (or effectively that), treat it as “run one cleanup session now”.

**No-loop rule:** every session must end with at least one concrete artifact:

- a `sorry` removed (proved or replaced by a named `axiom`/interface),
- or a refactor that **reduces assumption surface area** (fewer places importing a shim),
- or a documentation update in one of:
  - `REMAINING_WORK.md`
  - `PROOF_STATUS_CURRENT.md`
  - `REALITY_PORT_PLAN.md`

If none happens, the session is a failure: immediately downgrade scope and do a smaller cleanup.

## “Allowed assumptions” policy (explicitly OK)

The user is OK with keeping classical axioms. Prefer to place them in **one of these forms**:

- a `structure ...Assumptions` bundling the hypotheses,
- or a single `axiom ...` in a dedicated `*Shim.lean` file (with a docstring that names the intended theorem source).

Good candidates to remain axioms for now (if not already proved):

- **Boundary wedge closure (P+)** packages:
  - `ExplicitFormula/BoundaryWedgeInterfaces.lean`
  - `ExplicitFormula/PPlusZetaShim.lean` (currently the shim/axiom)
- **Outer existence / Poisson representation** packages:
  - `ExplicitFormula/OuterConstruction.lean` (already mostly “axioms + framework”)
- **Route 3 splice identity** (measure-first / `L²(μ_spec)` identity):
  - `ExplicitFormula/ContourToBoundary.lean`
  - `ExplicitFormula/PSCSplice.lean`
- **Zeta-specific boundary representation / phase–velocity plumbing** (if needed):
  - `ExplicitFormula/ZetaInstantiation.lean`
  - `ExplicitFormula/CayleyBridgeZeta.lean`

The key is: **no scattered `sorry`s**—make each hard input a single, named assumption with a clear role.

## The current cleanup backlog (pick ONE per session)

Choose exactly one and finish it end-to-end (including build + docs update if it changes status).

### A. Remove/relocate `sorry`s in `ExplicitFormula/`

Goal: reduce `sorry`s by converting them to explicit `axiom` declarations or by proving them.

**Status update (2025-12-19):** the `RiemannRecognitionGeometry/ExplicitFormula/*` subtree is now **`sorry`-free**.
The remaining gaps are explicit **axioms / hypothesis bundles** (Fourier inversion, wedge closure, splice identity inputs, etc.).

Focus order:

- `RiemannRecognitionGeometry/ExplicitFormula/ZetaInstantiation.lean`
- `RiemannRecognitionGeometry/ExplicitFormula/ZetaFourierInversionWeil.lean`
- `RiemannRecognitionGeometry/ExplicitFormula/ZetaDet2Weil.lean`
- `RiemannRecognitionGeometry/ExplicitFormula/WeilTestFunction.lean`
- `RiemannRecognitionGeometry/ExplicitFormula/OuterConstruction.lean` (now `sorry`‑free; remaining “boundary positivity” is an explicit axiom/interface)

Policy:

- If it’s “small Lean glue” (imports, simp, rewriting), **prove it**.
- If it’s real analysis/number theory, **replace it** with a named `axiom` and wire it through a bundle.

### B. Consolidate zeta end-to-end assumptions into one bundle

Goal: create/extend a single “end-to-end zeta run” assumptions record that:

- packages wedge/PPlus,
- packages splice identity assumptions (μ_spec identity),
- packages any remaining `ZetaInstantiation` glue assumptions,
- exposes a single theorem:
  - `... → RiemannHypothesis`

Prefer to do this by **using existing bundles** rather than inventing new abstractions.

**Status update (2025-12-19):** largely complete:

- `ExplicitFormula/ZetaInstantiation.lean` now concentrates ζ glue assumptions into named bundles:
  - `ZetaPSCGlue` (phase regularity/representation/velocity + outer regularity)
  - `ZetaRoute3Glue` (ratio identity + Cayley measure-bridge package)
  - `ZetaGlue` (convenience wrapper bundling the two)
- `ExplicitFormula/ZetaEndToEndSchwartz.lean` provides:
  - `ZetaInstantiation.EndToEnd.Assumptions` with `Azeta : ZetaInstantiation.Assumptions_zeta ...` (deduped L²/integrability plumbing)
  - `ZetaInstantiation.EndToEnd.AssumptionsSplice` + `ZetaInstantiation.EndToEnd.RH_of_splice` (boundary wedge + splice identity → RH)

### C. Reduce duplicate shims / unify naming

Goal: ensure “the same conceptual assumption” is not duplicated across:

- `Port/*` and `ExplicitFormula/*`
- `CayleyBridgeZeta.lean` and `ZetaInstantiation.lean`
- `PPlusZetaShim.lean` and other wedge-entrypoints

Action:

- keep the “real” interface in one place,
- make other files `abbrev`/re-export it (like `Port/WedgeClosure.lean` already does),
- delete or deprecate redundant shims (only if safe and small).

### D. Port: tighten the CR/Green “energy → phase” assumption surface (xi + cofactor)

Goal: keep the Port/RG pipeline faithful and explicit by factoring the CR/Green wall into
small “blueprint-shaped” interfaces (trace identity + pairing bound), rather than a monolithic
`ClassicalAnalysisAssumptions` record or scattered `sorry`s.

**Status update (2025-12-19):** partial progress landed (build green):

- **Strong targets exist**:
  - `Port.XiCRGreenAssumptionsStrong` / `Port.CofactorCRGreenAssumptionsStrong`
  - and conversion lemmas to the weaker (E-quantified) APIs.
- **Faithful S2 interfaces exist on both sides** (trace identity + pairing bound):
  - cofactor: `RiemannRecognitionGeometry/Port/CofactorCRGreenS2Interfaces.lean` + `.../CofactorCRGreenS2.lean`
  - xi: `RiemannRecognitionGeometry/Port/XiCRGreenS2Interfaces.lean` + `.../XiCRGreenS2.lean`
- **Wiring glue exists**:
  - `RiemannRecognitionGeometry/Port/EnergyCRGreenS2.lean`: `(xi S2 + cofactor S2) → EnergyCRGreenAssumptionsStrong`
  - `RiemannRecognitionGeometry/Port/MainNoRGAssumptions.lean` now has
    `RiemannHypothesis_recognition_geometry_of_oscillationTarget_of_S2`.

Remaining work for this backlog item is **not** Lean plumbing anymore; it is the analytic content:
produce real instances of the S2 interfaces from a concrete window choice + Green pairing +
`Port/SkewHarmGate.lean` boundary-term gates + Cauchy–Schwarz.

## Always-run checklist (every session)

1. **Pick scope** (one backlog item).
2. **Edit Lean files** (minimal diff; one concept per edit).
3. **Run build**:
   - `cd /Users/jonathanwashburn/Projects/riemann-geometry-rs && lake build`
4. **Update tracking docs** (only if status materially changed):
   - `REMAINING_WORK.md`
   - `PROOF_STATUS_CURRENT.md`
   - `REALITY_PORT_PLAN.md`

## What “done” looks like for second-tier cleanup

This cleanup track is “done enough” when:

- `lake build` is green,
- there are **no `sorry`s** in the main entrypoints (even if some axioms remain),
- every remaining unproved analytic input is represented as a **named assumption** in a small number of files,
- the docs clearly say which assumptions are the remaining blockers.


