# Remaining Work (current + historical)

## Current status (2025-12-18)

**Build**: `lake build` succeeds.

### What the repo proves today (honest summary)

- **Recognition Geometry (RG) track**: `RiemannRecognitionGeometry/Main.lean` proves RH **conditional** on explicit hypothesis bundles:
  - **Oscillation certificate**: `OscillationTarget := ∃ M, InBMOWithBound logAbsXi M ∧ M ≤ C_tail`
    (`RiemannRecognitionGeometry/Assumptions.lean`)
  - **Classical analysis inputs** (kept explicit): `ClassicalAnalysisAssumptions` (Green/CR bounds, ζ≠0 on (0,1))
    (`RiemannRecognitionGeometry/Assumptions.lean`)
  - **RG-specific bottleneck** (the big one): `RGAssumptions.j_carleson_energy_axiom_statement`
    (`RiemannRecognitionGeometry/Assumptions.lean`)

- **Route 3 / ExplicitFormula track**: maintained separately under `RiemannRecognitionGeometry/ExplicitFormula/*`
  and driven by `ROUTE3_DRIVER.md` (assumption ledger + track workflow).

### What is no longer a blocker (closed relative to older notes)

- **Arctan/phase machinery**: `RiemannRecognitionGeometry/Axioms.lean` has **0 `sorry`**; mixed-sign edge issues were refactored away by proving the *needed bounds* directly.
- **Whitney width control**: `RiemannRecognitionGeometry/WhitneyGeometry.lean` provides `dyadic_interval_with_width`, giving both lower/upper width control.
- **No real zeros on (0,1)**: handled via `RiemannRecognitionGeometry/DirichletEta.lean` (still uses a standard identity-principle axiom to connect η and ζ for `0<s<1`).

### The actual remaining “unconditional” gaps

- **(G1) Discharge the RG bottleneck**: prove `RGAssumptions.j_carleson_energy_axiom_statement` (or replace it with a theorem) using a Hardy/Dirichlet/Carleson/CR–Green pipeline.
- **(G2) Produce an explicit oscillation certificate**: prove `OscillationTarget` for `logAbsXi`.
- **(G3) Reduce (or justify) remaining classical-analysis axioms** in compiled modules (e.g. John–Nirenberg/CZ scaffolding, Fefferman–Stein embedding, η–ζ identity principle).

Current implementation direction for **(G1)**: start with **Fefferman–Stein + BMO inheritance** (see `REALITY_PORT_PLAN.md` §5), using the new `RiemannRecognitionGeometry/Port/*` interfaces as the faithful targets.

As of now, the **Carleson-budget** side has landed for `Ebox := Port.cofactorEbox_poisson`
(see `RiemannRecognitionGeometry/Port/CofactorCarlesonBudget.lean`). The remaining key port target is the
**CR/Green** side: `HardyDirichletCRGreen cofactorEbox_poisson`.

Concretely, “CR/Green” here means: choose a scale-normalized window `φ_I`, prove a scale-invariant window-energy
bound for its Poisson extension, establish the Green pairing (boundary phase velocity ↔ interior pairing),
kill the boundary term at infinity (use `Port/SkewHarmGate.lean`), then apply Cauchy–Schwarz to obtain the
energy→phase-change inequality.

**Update (upper bound side)**: we also introduced an explicit *energy-based* xi-phase CR/Green target
`Port.XiCRGreenAssumptions` and a derived theorem `Port.totalPhaseSignal_bound_of_xiCRGreenAssumptions`,
so the Port contradiction chain can now be run without the monolithic `ClassicalAnalysisAssumptions` record.

For symmetry, `Port/XiCarlesonBudget.lean` instantiates the same Hardy/Dirichlet Carleson-budget interface on the
xi side (wrapping `xiEbox_poisson` as `xiEbox_poissonEbox`), so “upper bound” and “lower bound” routes share the
same budget abstraction.

We also added an explicit “blueprint-shaped” upper bound lemma in `Port/TotalPhaseSignalBound.lean` that derives
`totalPhaseSignal ≤ U_tail` from the Hardy/Dirichlet Carleson-budget interface + the xi CR/Green target (in the
“interval contains a zero” setting).

For convenience, the two energy-based CR/Green targets are now bundled as
`Port.EnergyCRGreenAssumptions`, and Port “main” theorems have wrappers that take that single bundle.

To match the `reality` CR/Green blueprint style (real-valued phase differences / pairings), we also added
`Port.RealPhaseTransfer`: a small algebraic layer that transfers bounds from ℝ-valued phase differences
(`argXi` / “real cofactor phase”) to the `Real.Angle` norms used by the RG spine.

We also added “blueprint-style” Port wrappers (in `Port/ZeroFreeWithInterval.lean` and `Port/MainNoRGAssumptions.lean`)
that take these real-valued CR/Green targets directly, and then transfer internally.

For convenience, these real-valued CR/Green targets are now bundled as
`Port.EnergyCRGreenAssumptionsReal`.

### How `/Projects/reality` helps (porting plan)

See `REALITY_PORT_PLAN.md` for a statement-by-statement alignment with:
`/Users/jonathanwashburn/Projects/reality/IndisputableMonolith/RH/HardyDirichlet/*.lean.disabled`
and `/Users/jonathanwashburn/Projects/reality/IndisputableMonolith/CPM/LawOfExistence.lean`.

**Note**: the `reality` Hardy/Dirichlet files are blueprint scaffolds (they still contain `sorry`/axiom placeholders for
the real analytic content), so the remaining work here is to *formalize* CR/Green + window-energy estimates in this repo,
or keep them as explicit target interfaces (`Port.*CRGreenAssumptions*`).

### Port scaffold (implemented)

Translation-stub modules (compiled in this repo) now exist under `RiemannRecognitionGeometry/Port/`:
- `HardyDirichletCarleson.lean`: a faithful **Carleson energy budget** interface (parameterized by an abstract box-energy functional), taking an explicit BMO certificate `InBMOWithBound (cofactorLogAbs ρ) M` as input.
- `HardyDirichletCRGreen.lean`: a faithful **CR/Green cofactor phase bound** interface (energy → phase bound).
  (Note: this interface is currently **cofactor-specific**; the xi-side uses `Port.XiCRGreenAssumptions*`.)
- `SkewHarmGate.lean`: a reusable **boundary-term at ∞ vanishes from integrability** wrapper, matching the pattern used in the `reality` repo.
- `WeierstrassTailBound.lean`: a derived theorem `weierstrass_tail_bound_of_hardyDirichlet` showing the RG tail bound follows from the two Hardy/Dirichlet-style interfaces + the √|I| cancellation.
- `CofactorEnergy.lean`: concrete candidates `Ebox` for the cofactor field:
  - `cofactorEbox` (via `CarlesonBound.boxEnergy` of `poissonExtension_gradient`), and
  - `cofactorEbox_poisson` (via `PoissonExtension.carleson_energy`; matches the Fefferman–Stein axiom interface).
- `CofactorCarlesonBudget.lean`: proves `HardyDirichletCarlesonBudget cofactorEbox_poisson` from the existing Fefferman–Stein axiom `PoissonExtension.bmo_carleson_embedding`.
- `CofactorTailBound.lean`: derives an RG-style cofactor tail bound from
  `HardyDirichletCarlesonBudget cofactorEbox_poisson` plus a CR/Green interface; it now exposes variants depending on
  either an explicit `HardyDirichletCRGreen cofactorEbox_poisson` or the energy-based `CofactorCRGreenAssumptions`
  bundle, while keeping the original `ClassicalAnalysisAssumptions`-based theorem as a compatibility wrapper.
- `BlaschkeDominatesTotal.lean`: an RG-facing theorem `Port.blaschke_dominates_total_of_cofactorBMO` that removes the `RGAssumptions` dependency from “Blaschke dominates total” and instead takes the explicit cofactor BMO certificate.
- `BlaschkeDominatesTotal.lean` also has variants that depend only on the energy-based `Port.CofactorCRGreenAssumptions`
  target bundle (rather than the full `ClassicalAnalysisAssumptions` record).
- `ZeroFreeWithInterval.lean`: a centered contradiction theorem `Port.zero_free_with_interval_of_cofactorBMO` that removes the `RGAssumptions` dependency from `Axioms.zero_free_with_interval` (at the cost of also assuming cofactor BMO).
- `CofactorCRGreenAssumptions.lean`: packages the remaining “CR–Green” step as an **energy-based** target tied to
  `cofactorEbox_poisson` (compatible with the older project-level `cofactor_green_identity_axiom_statement`, but
  designed to be replaced by a faithful Green pairing proof).
- `CofactorBMOInheritance.lean`: packages the missing “BMO inheritance” bridge (logAbsXi → cofactorLogAbs) as an
  explicit target interface. **Update**: with the corrected Port cofactor boundary-modulus model (`cofactorLogAbs ρ = logAbsXi`),
  this inheritance is now definitionally trivial (`cofactorBMOInheritance_trivial`), and the Port contradiction has
  convenience wrappers that take only `OscillationTarget`.
- `MainNoRGAssumptions.lean`: Port analogues of the RG “main” theorems without `RGAssumptions`.
  **Update**: now also has “trivial inheritance” convenience wrappers (no explicit `CofactorBMOInheritance` argument).
- `LocalZeroFree.lean`: mirrors the RG band-interior “no zeros” step (`local_zero_free` / `no_interior_zeros`) but
  removes the `RGAssumptions` parameter by routing through the Port centered contradiction + `CofactorBMOInheritance`.
- `WedgeClosure.lean` / `SchurPinch.lean` (Port): alignment wrappers that re-export the existing Route 3
  boundary-wedge and Schur pinch interfaces via stable `Port/*` paths (matching the `reality` module shapes).
- `Port.lean`: aggregator module so the whole Port surface can be compiled as one target (`lake build RiemannRecognitionGeometry.Port`).

---

## Historical notes (superseded by the current refactor)

The remainder of this file is preserved for context, but its “N sorries” accounting and specific line references
no longer describe the current Lean development.

### Snapshot (older)

**Current Status: 10 sorries**

#### Analysis Complete, Implementation Pending

**1. Same-sign phase bounds (Axioms lines 546, 567)**
- Mathematical approach identified:
  - For σ < a case: y = (a-σ)/γ < 1 (proven: σ < a ≤ γ implies a - σ < γ)
  - For x - y ≥ 1 and y < 1: use arctan subtraction formula
  - arctan(x) - arctan(y) = arctan((x-y)/(1+xy)) ≥ arctan(1/3)
  - 2 * arctan(1/3) > L_rec ✓
- Need: Import/prove arctan subtraction formula from Mathlib
  - `Real.arctan_add` exists, need to derive subtraction version

**2. σ > b case (Axioms line 567)**
- Similar to σ < a but need different bound
- May require additional geometric constraint on how far σ can be from [a,b]

#### Require Classical Analysis

**3. zero_has_nonzero_im (Axioms line 780)**
- Need: ζ(s) ≠ 0 for real s ∈ (0, 1)
- Approach: ζ(s) < 0 on (0,1) via Dirichlet eta function
- Effort: ~70 lines, not currently in Mathlib

**4. blaschke_dominates_total (Axioms line 886)**
- The main BMO→Carleson embedding theorem
- Effort: ~300 lines of classical analysis
- Components: Weierstrass factorization, BMO norm bound, Fefferman-Stein

**5. whitney_interval_width (Main line 98)**
- Need: 2 * I.len ≥ |ρ.im| for covering interval
- Issue: Current construction chooses scale based on Re(ρ), not Im(ρ)
- Fix: Modify coveringBand to use max(3(σ-1/2), |ρ.im|/2)

#### Formula Corrections

**6-7. Mixed-sign formula (Axioms lines 230, 239)**
- Issue: phaseChange formula differs by ±π for mixed-sign cases
- Edge cases (a=σ, b=σ) already proven
- General case needs careful branch cut analysis

**8-10. Negative γ phase bounds (Axioms lines 683, 693, 695)**
- Symmetric to γ > 0 cases
- Need same arctan machinery

#### Proof Architecture (Sound)

```
RH ← no_off_critical_zeros_in_strip ← local_zero_free
                                          ├── blaschke_lower_bound (≥ L_rec)
                                          │     └── phase_bound_from_arctan
                                          ├── blaschke_dominates_total
                                          ├── totalPhaseSignal_bound (≤ U_tail)
                                          └── L_rec > 4 * U_tail ✅
```

The contradiction follows because:
- Blaschke contribution B ≥ L_rec ≈ 0.55
- Total phase signal R ≤ U_tail ≈ 0.13
- But B is part of R, so L_rec ≤ |B| ≤ |R| ≤ U_tail
- Contradiction since L_rec > U_tail ✅ (proven)

#### Priority Order for Completion

1. **Arctan machinery** (~50 lines) - Unblocks 5 sorries
2. **Whitney width fix** (~30 lines) - Structural fix
3. **ζ ≠ 0 on (0,1)** (~70 lines) - Classical result
4. **BMO→Carleson** (~300 lines) - Major undertaking
