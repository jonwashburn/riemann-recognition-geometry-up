## Reality → riemann-geometry-rs port plan (Lean)

This note is the “alignment layer” between:

- This repo (`riemann-geometry-rs`): the **Recognition Geometry** and **Route 3 (ExplicitFormula)** Lean developments.
- The local repo at `/Users/jonathanwashburn/Projects/reality`: the **IndisputableMonolith/RH/HardyDirichlet** blueprint files and the **CPM** core.

The goal here is not to claim anything is already proved in `reality/`—most of the RH/HardyDirichlet files are `.lean.disabled` and contain placeholders—but to line up the **exact statement-shapes** so we can port work surgically.

### 1) What’s “done” in this repo (current main spine)

#### Recognition Geometry spine

- **Entry point**: `RiemannRecognitionGeometry/Main.lean`
- **Status**: the RG chain **builds** and is **structurally complete**, but it is explicitly **conditional**.
- **Important refactor already landed**:
  - `RiemannRecognitionGeometry/Axioms.lean` has **0 `sorry`**.
  - `RiemannRecognitionGeometry/WhitneyGeometry.lean` replaces the old “width” gap with a dyadic interval selector proving **both** lower and upper width bounds.
  - “No real zeros on (0,1)” is routed through `RiemannRecognitionGeometry/DirichletEta.lean` (still uses an identity-principle axiom; see below).

#### Route 3 / ExplicitFormula spine

- **Driver**: `ROUTE3_DRIVER.md`
- **Code**: `RiemannRecognitionGeometry/ExplicitFormula/*`
- **Status**: there are still **`sorry`** and **axioms** in this track; it’s explicitly managed via hypothesis bundles and an assumption ledger.

### 2) The real remaining gaps in *this* repo (exact Lean targets)

The “big one” is not a missing lemma anymore—it’s a **bundled assumption surface** that we want to discharge (or at least tighten) by porting/matching the HardyDirichlet pipeline.

#### 2.1 The RG bottleneck estimate (what “Blaschke dominates total” reduces to)

In RG, the analytic core is packaged as:

- `RGAssumptions.j_carleson_energy_axiom_statement`
  - File: `RiemannRecognitionGeometry/Assumptions.lean`
  - Meaning: **for each Whitney interval** \(I\) around a zero-height and parameter \(M\), there exists an energy constant \(E\) with \(E \le K_{\mathrm{tail}}(M)\).

This is then fed into the *derived* tail bound:

- `Conjectures.weierstrass_tail_bound_axiom_statement`
  - File: `RiemannRecognitionGeometry/Conjectures.lean`
  - Meaning: the **cofactor phase change** is bounded by `U_tail M`, and hence the “tail correction” to the Blaschke phase is small.

Finally, `Axioms.blaschke_dominates_total(_centered)` turns that into the contradiction-ready inequality
`totalPhaseSignal I ≥ L_rec - U_tail M`.

#### 2.2 The “Green/CR” analytic input is explicit

RG separates:

- **Classical** Green/Cauchy–Schwarz bound, as a *field*:
  - `ClassicalAnalysisAssumptions.cofactor_green_identity_axiom_statement`
  - File: `RiemannRecognitionGeometry/Assumptions.lean`

This is the exact “CR–Green pairing + Cauchy–Schwarz” interface we want to match from the `reality/` blueprints.

#### 2.3 The oscillation certificate is the other major missing ingredient

The RG main theorem is conditional on:

- `OscillationTarget := ∃ M, InBMOWithBound logAbsXi M ∧ M ≤ C_tail`
  - File: `RiemannRecognitionGeometry/Assumptions.lean`

So even if we prove the Carleson/Green interface, we still need to justify an explicit BMO/oscillation bound for `logAbsXi`.

#### 2.4 Global axioms still present in the compiled library

As of today, the repo still contains global `axiom` declarations in compiled modules, mainly:

- **CZ/JN infrastructure**: `RiemannRecognitionGeometry/JohnNirenberg.lean`
- **η–ζ identity principle (s<1)**: `RiemannRecognitionGeometry/DirichletEta.lean`
- **BMO→Carleson embedding**: `RiemannRecognitionGeometry/PoissonExtension.lean`

These are “expected classical analysis” axioms, but they are still axioms and should be tracked as such.

### 3) What’s in `reality/` that matches these gaps (blueprint alignment)

All paths below are in the local repo:
`/Users/jonathanwashburn/Projects/reality/`.

#### 3.1 HardyDirichlet pipeline (the on-the-nose blueprint)

- **Carleson/BMO/energy budget**: `IndisputableMonolith/RH/HardyDirichlet/Carleson.lean.disabled`
  - Key blueprint statements (placeholders right now):
    - `Fefferman_Stein`: boundary BMO → tent energy bound
    - `VK_to_Carleson`: VK density → global budget `K_ξ ≤ 0.16`
    - `tent_energy_bound`: `E_I(U) ≤ K_ξ · |I|`
  - **Maps to this repo**:
    - `RGAssumptions.j_carleson_energy_axiom_statement`
    - (and/or) `PoissonExtension.bmo_carleson_embedding` depending on which route we take

- **CR/Green pairing**: `IndisputableMonolith/RH/HardyDirichlet/CRGreen.lean.disabled`
  - Key blueprint statements:
    - `Green_pairing`: boundary pairing equals interior energy pairing
    - `Cauchy_Schwarz_bound`: `|∫ φ_I W'| ≤ C_geom · √E_I(U)`
  - **Maps to this repo**:
    - `ClassicalAnalysisAssumptions.cofactor_green_identity_axiom_statement`

- **Numerical/plateau closure**: `IndisputableMonolith/RH/HardyDirichlet/WedgeClosure.lean.disabled`
  - Key blueprint statements:
    - `plateau_uniform` (Poisson plateau lower bound)
    - `wedge_closure : Upsilon < 1/2`
    - `wedge_implies_boundary_positivity`
  - **Maps to this repo**:
    - RG’s numeric closure lemmas (`U_tail(C_tail) < L_rec/2`, etc.)
    - the “plateau” component is analogous to RG’s explicit arctan lower bounds

- **Schur pinch completion**: `IndisputableMonolith/RH/HardyDirichlet/SchurPinch.lean.disabled`
  - This is an *alternative global closure argument* (maximum modulus for a Schur transform).
  - Even if RG remains the main line here, this file is valuable as a cross-check of how the
    Carleson/Green bounds are meant to be used downstream.

#### 3.2 CPM core that matches the “dispersion slot” story

- `IndisputableMonolith/CPM/LawOfExistence.lean`
  - The relevant interface is the `Model.dispersion` field:
    `orthoMass a ≤ Cdisp * tests a`.
  - In RG language, this is the “total noise ≤ tail budget” inequality; in our repo it is
    represented by the combination:
    - energy budget (`RGAssumptions.j_carleson_energy_axiom_statement`)
    - Green bound (`ClassicalAnalysisAssumptions.cofactor_green_identity_axiom_statement`)
    - length cancellation (`sqrt_energy_cancellation` in `Conjectures.weierstrass_tail_bound_axiom_statement`)

#### 3.3 A reusable technical pattern: boundary-term gates

- `IndisputableMonolith/NavierStokes/SkewHarmGate.lean`
  - Contains a concrete pattern for:
    - integration-by-parts identities with explicit boundary terms, and
    - a lemma deriving “boundary term → 0 at ∞” from integrability (`zeroSkewAtInfinity_of_integrable`).
  - This is directly relevant for formalizing “no boundary export” steps in CR/Green arguments.

### 4) A concrete porting strategy (minimal, statement-driven)

#### 4.1 Decide the target interface to discharge first

Start with the **smallest** “big win” interface:

- **Target A (RG bottleneck)**: prove `RGAssumptions.j_carleson_energy_axiom_statement` for the specific RG cofactor field.
  - This is the minimal statement needed to remove the last RG-specific conjecture.

Then:

- **Target B (classical Green input)**: prove `ClassicalAnalysisAssumptions.cofactor_green_identity_axiom_statement`.
  - This is classical and should be ported from the `CRGreen` blueprint + Mathlib integration lemmas.

Finally:

- **Target C (oscillation certificate)**: produce an `OscillationTarget` for `logAbsXi`.
  - This is the truly “unconditional bottleneck” for the RG chain in this repo.

#### 4.2 Map `HardyDirichlet` objects to existing RG objects

In this repo, the “cofactor phase” is already abstracted as:

- `rgCofactorPhaseAngle ρ t := phaseXi t + (rgBlaschkePhase ρ t : Real.Angle)`
  - File: `RiemannRecognitionGeometry/Phase.lean`

So porting work should aim to produce **bounds on phase changes of that object** (mod \(2π\)),
not bounds about `Complex.arg` directly.

#### 4.3 Keep the import surface small

Porting from `reality/` should be done by copying *statements and proof fragments* into new files here,
not by trying to add `reality/` as a Lake dependency immediately. The disabled files are a blueprint,
not a compilable library.

Suggested landing files in this repo (new):

- ✅ `RiemannRecognitionGeometry/Port/HardyDirichletCarleson.lean` (energy budget interface; mirrors `reality/.../Carleson.lean.disabled`)
- ✅ `RiemannRecognitionGeometry/Port/HardyDirichletCRGreen.lean` (Green/CR interface; mirrors `reality/.../CRGreen.lean.disabled`)
- ✅ `RiemannRecognitionGeometry/Port/SkewHarmGate.lean` (boundary-term-at-∞ gate pattern; mirrors `reality/.../SkewHarmGate.lean`)
- ✅ `RiemannRecognitionGeometry/Port/WeierstrassTailBound.lean` (derives the RG tail bound from the two Hardy/Dirichlet-style interfaces + √|I| cancellation)
- ✅ `RiemannRecognitionGeometry/Port/CofactorEnergy.lean` (defines concrete candidates:
  - `cofactorEbox` via `CarlesonBound.boxEnergy` of `poissonExtension_gradient`, and
  - `cofactorEbox_poisson` via `PoissonExtension.carleson_energy` (matches the Fefferman–Stein axiom interface))

### 5) Immediate next actions

1. ✅ Extracted the key statement-shapes from `reality/.../HardyDirichlet/*.lean.disabled` and added
   compiled translation stubs in `RiemannRecognitionGeometry/Port/` (see above).
2. ✅ Decision (first route to try): **Fefferman–Stein + BMO inheritance**.
   - Rationale: this repo already has scale-correct BMO infrastructure (`InBMOWithBound`) and a
     Fefferman–Stein-style axiom (`PoissonExtension.bmo_carleson_embedding`), so the shortest path is:
     `BMO(log|cofactor|) → Carleson energy budget → CR/Green → tail bound`.
   - The VK/zero-density route remains a fallback (and is modeled in the `reality` blueprint).
3. ✅ Defined a concrete “cofactor energy” functional `Ebox` (see `Port/CofactorEnergy.lean`).
   Next: start discharging:
   - `HardyDirichletCarlesonBudget Ebox` from BMO + Fefferman–Stein, and
   - `HardyDirichletCRGreen Ebox` from Green pairing + boundary-term gates (use `Port/SkewHarmGate.lean`).

**Update**: the Carleson side has started landing:
- ✅ `RiemannRecognitionGeometry/Port/CofactorCarlesonBudget.lean` proves
  `hardyDirichletCarlesonBudget_cofactorEbox_poisson : HardyDirichletCarlesonBudget cofactorEbox_poisson`
  using only the existing Fefferman–Stein axiom `PoissonExtension.bmo_carleson_embedding` and the BMO certificate
  provided as an input to the interface.
- ✅ `RiemannRecognitionGeometry/Port/CofactorTailBound.lean` shows how to combine:
  `HardyDirichletCarlesonBudget cofactorEbox_poisson` + a (placeholder) cofactor CR/Green interface +
  `Port.weierstrass_tail_bound_of_hardyDirichlet` to recover an RG-style tail bound.
  It now exposes tail-bound variants depending on either:
  - an explicit `HardyDirichletCRGreen cofactorEbox_poisson`, or
  - the energy-based `Port.CofactorCRGreenAssumptions` bundle,
  and keeps the old `ClassicalAnalysisAssumptions`-based theorem as a compatibility wrapper.
- ✅ `RiemannRecognitionGeometry/Port/BlaschkeDominatesTotal.lean` wires the Port tail bound into the RG spine:
  it proves `Port.blaschke_dominates_total_of_cofactorBMO`, a drop-in replacement of
  `Axioms.blaschke_dominates_total` that removes the `RGAssumptions` dependency and takes an explicit
  cofactor BMO certificate instead.
  It also now provides variants that depend only on the **energy-based** CR/Green target bundle
  `Port.CofactorCRGreenAssumptions` (rather than `ClassicalAnalysisAssumptions`).
- ✅ `RiemannRecognitionGeometry/Port/ZeroFreeWithInterval.lean` adds
  `Port.zero_free_with_interval_of_cofactorBMO`, a centered contradiction theorem that removes the
  `RGAssumptions` dependency from `Axioms.zero_free_with_interval` (it still uses the upper bound
  `totalPhaseSignal_bound` from `logAbsXi` BMO).
- ✅ `RiemannRecognitionGeometry/Port/LocalZeroFree.lean` mirrors the RG band-interior “no zeros” step
  (`Axioms.local_zero_free` / `Axioms.no_interior_zeros`) but removes the `RGAssumptions` parameter,
  routing the contradiction through the Port centered theorem plus the cofactor BMO inheritance interface.
- ✅ `RiemannRecognitionGeometry/Port/WedgeClosure.lean` and `RiemannRecognitionGeometry/Port/SchurPinch.lean`:
  lightweight **alignment wrappers** that re-export the already-present Route 3 boundary-wedge and Schur pinch
  interfaces (ported from `riemann-finish`) via stable `Port/*` paths, matching the shape of the `reality`
  `WedgeClosure` / `SchurPinch` modules.
- Remaining: discharge the **CR/Green** interface for the cofactor phase (the hard “Green pairing” bookkeeping).
  - ✅ New explicit target bundle: `RiemannRecognitionGeometry/Port/CofactorCRGreenAssumptions.lean` packages the
    CR/Green step as an energy-based assumption tied to `cofactorEbox_poisson` (and provides a compatibility lemma
    from the existing project-level `ClassicalAnalysisAssumptions.cofactor_green_identity_axiom_statement`).
  - ✅ New explicit target bundle: `RiemannRecognitionGeometry/Port/CofactorBMOInheritance.lean` packages the other
    missing bridge needed to *use* the Port route in the RG spine: BMO inheritance
    `InBMOWithBound logAbsXi M → InBMOWithBound (cofactorLogAbs ρ) M` (currently as a target interface).


