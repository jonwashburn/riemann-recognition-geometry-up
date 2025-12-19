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
- **Status**: this track is now **`sorry`-free**; the remaining gaps are explicit **axioms / hypothesis bundles** (wedge closure, Fourier inversion, splice identity inputs, etc.), and are managed via the assumption ledger.

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
 - ✅ `RiemannRecognitionGeometry/Port/XiCRGreenS2Interfaces.lean` + `.../XiCRGreenS2.lean`:
   faithful xi-side “S2” (trace identity + pairing bound) interfaces, matching the blueprint decomposition.
 - ✅ `RiemannRecognitionGeometry/Port/EnergyCRGreenS2.lean`:
   wiring glue `(xi S2 + cofactor S2) → EnergyCRGreenAssumptionsStrong`, plus a Port main wrapper
   `RiemannHypothesis_recognition_geometry_of_oscillationTarget_of_S2` in `Port/MainNoRGAssumptions.lean`.

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
- ✅ `RiemannRecognitionGeometry/Port/MainNoRGAssumptions.lean`: Port analogues of the RG “main” theorems
  (no-off-critical-zeros in the strip, and the conditional RH theorem) **without `RGAssumptions`**.
  **Update**: since `cofactorLogAbs ρ = logAbsXi` in the current Port model, it now also provides
  “trivial inheritance” convenience wrappers (no explicit `CofactorBMOInheritance` argument).
- ✅ `RiemannRecognitionGeometry/Port/WedgeClosure.lean` and `RiemannRecognitionGeometry/Port/SchurPinch.lean`:
  lightweight **alignment wrappers** that re-export the already-present Route 3 boundary-wedge and Schur pinch
  interfaces (ported from `riemann-finish`) via stable `Port/*` paths, matching the shape of the `reality`
  `WedgeClosure` / `SchurPinch` modules.
- ✅ `RiemannRecognitionGeometry/Port.lean`: aggregator module that imports all `Port/*` modules so they can be
  compiled/checked together (`lake build RiemannRecognitionGeometry.Port`).
- Remaining: discharge the **CR/Green** interface for the cofactor phase (the hard “Green pairing” bookkeeping).
  - ✅ New explicit target bundle: `RiemannRecognitionGeometry/Port/CofactorCRGreenAssumptions.lean` packages the
    CR/Green step as an energy-based assumption tied to `cofactorEbox_poisson` (and provides a compatibility lemma
    from the existing project-level `ClassicalAnalysisAssumptions.cofactor_green_identity_axiom_statement`).
  - ✅ New explicit target bundle (upper bound side): `RiemannRecognitionGeometry/Port/XiCRGreenAssumptions.lean`
    packages the **xi-phase** CR/Green step as an energy-based assumption tied to
    `Port.xiEbox_poisson` (`Port/XiEnergy.lean`).
  - ✅ New theorem: `RiemannRecognitionGeometry/Port/TotalPhaseSignalBound.lean` proves an energy-based Port analogue
    of `Axioms.totalPhaseSignal_bound`, using only:
    - the existing Fefferman–Stein axiom `PoissonExtension.bmo_carleson_embedding`, and
    - `Port.XiCRGreenAssumptions`,
    yielding `totalPhaseSignal I ≤ U_tail M`.
  - ✅ Also in `Port/TotalPhaseSignalBound.lean`: a Hardy/Dirichlet-budget-based variant
    `totalPhaseSignal_bound_of_hardyDirichletCarlesonBudget_xiEbox_poisson`, exhibiting the exact
    blueprint shape “Carleson budget + CR/Green ⇒ phase bound” (in the “interval contains a zero” setting).
  - ✅ Symmetry: `RiemannRecognitionGeometry/Port/XiCarlesonBudget.lean` instantiates the Hardy/Dirichlet
    Carleson-budget interface for the xi energy functional (wrapped as `xiEbox_poissonEbox`), so both the
    “upper bound” and “lower bound” sides share the same budget abstraction.
  - ✅ New Port main theorems: `RiemannRecognitionGeometry/Port/MainNoRGAssumptions.lean` now also provides a
    full “no RGAssumptions / no ClassicalAnalysisAssumptions record” route, driven by
    `XiCRGreenAssumptions` + `CofactorCRGreenAssumptions` + `OscillationTarget`.
  - ✅ Convenience bundle: `RiemannRecognitionGeometry/Port/EnergyCRGreenAssumptions.lean` packages the two
    energy-based CR/Green targets into one record, and adds wrappers so Port “main” theorems can take a single
    assumption argument.
  - ✅ Transfer layer: `RiemannRecognitionGeometry/Port/RealPhaseTransfer.lean` adds purely algebraic lemmas
    that let us prove `Real.Angle` phase bounds from **real-valued** phase difference bounds (matching the
    `reality` CR/Green blueprint style). It also introduces “real-valued CR/Green targets” that imply the
    existing energy-based `XiCRGreenAssumptions` / `CofactorCRGreenAssumptions`.
  - ✅ New wrappers: Port centered contradiction and Port main RH theorems now have “blueprint-style”
    versions that take `XiCRGreenAssumptionsReal` / `CofactorCRGreenAssumptionsReal` directly, and then
    transfer to `Real.Angle` internally via `Port.RealPhaseTransfer`.
  - ✅ Convenience bundle (real-valued): `RiemannRecognitionGeometry/Port/EnergyCRGreenAssumptionsReal.lean`
    packages the two **real-valued** CR/Green targets into one record and adds wrappers that take that bundle.
  - Next proof-shape to port (faithful route, mirroring `reality/.../CRGreen.lean.disabled`):
    - **(i) Window/plateau choice**: define a smooth mean-zero window `φ_I` adapted to a Whitney interval `I`
      (scale \(L^2\) normalized so the eventual \(\sqrt{|I|}\) cancellation occurs).
    - **(ii) Window energy**: prove a scale-invariant bound on the weighted energy of the Poisson extension `V_I`
      (this is where the explicit constant `C_geom` comes from; in the blueprint it is Fourier/Plancherel).
    - **(iii) Green pairing**: show the boundary pairing with phase velocity equals an interior pairing
      \(\iint_{Q(I)} \nabla U \cdot \nabla V_I\) plus boundary terms.
    - **(iv) Boundary-term gate**: discharge the “boundary at ∞” term using the `Port/SkewHarmGate.lean` pattern
      (integrability/energy ⇒ boundary term tends to 0).
    - **(v) Cauchy–Schwarz**: apply C–S in the weighted energy space to get the final energy→phase bound.
    - **(vi) Package**: produce a genuine instance of `HardyDirichletCRGreen cofactorEbox_poisson`
      (i.e. prove `Port.CofactorCRGreenAssumptions` without routing through the existing axiom field).

  - **Reality status check (Dec 18)**: inspected
    `reality/IndisputableMonolith/RH/HardyDirichlet/CRGreen.lean.disabled` and
    `.../Carleson.lean.disabled` — they are **blueprints** (contain `sorry`/axiom placeholders for
    `standardWindow`, `Green_pairing`, `window_energy_bound`, Fefferman–Stein, VK→Carleson, etc.).
    So the remaining work here is **not** a “copy proofs over” task; it’s either:
    - genuinely formalize these analytic estimates in this repo / Mathlib, or
    - keep them as explicit target interfaces (`XiCRGreenAssumptions*`, `CofactorCRGreenAssumptions*`).

**Current status**: the CR/Green step is now fully isolated as *two* explicit energy-based targets:

- **Upper bound (xi phase)**: `Port.XiCRGreenAssumptions` + derived
  `Port.totalPhaseSignal_bound_of_xiCRGreenAssumptions`.
- **Lower bound (cofactor phase)**: `Port.CofactorCRGreenAssumptions` + derived Port tail bound route.

So the remaining analytic work is to prove these two CR/Green targets faithfully (Green pairing + window energy
bound + boundary-term-at-∞ gate + C–S), rather than routing through `ClassicalAnalysisAssumptions`.

**Implementation note (Dec 18)**: `Port/HardyDirichletCRGreen.lean` is currently **cofactor-specific**
(`rgCofactorPhaseAngle` bound). The xi-side CR/Green target remains separate as
`Port.XiCRGreenAssumptions` / `Port.XiCRGreenAssumptionsReal`.
- ✅ `RiemannRecognitionGeometry/Port/CofactorBMOInheritance.lean`: **resolved for the current Port model**.
  We corrected the cofactor boundary-modulus modeling (`cofactorLogAbs ρ = logAbsXi`, matching the fact that the
  half-plane Blaschke factor is unimodular on `Re s = 1/2`), so the “inheritance” bridge is definitionally trivial
  (`cofactorBMOInheritance_trivial`), and Port contradiction theorems now have convenience wrappers that take only
  `OscillationTarget`.


