## Proof soundness plan (recursive)

This document is meant to be pasted back into the assistant as a **recursive prompt**. The assistant should follow it **top-to-bottom**, always working on the **first unchecked checkbox**, until the “Definition of done” is satisfied.

### Non-negotiable constraints
- **Keep classical axioms**: Lean’s classical logic/choice axioms are fine, and we will also keep “classical analysis” results as explicit axioms (e.g. Fefferman–Stein, Green identity, identity principle for η/ζ), *as long as they are not formulated in a way that contradicts standard analysis / Mathlib.*
- **Zero inconsistent axioms in the build graph**: do not leave an inconsistent axiom in any module that is compiled by `lake build`.
- **No “make it true by definition” in the main chain**: placeholder definitions are allowed only if they are clearly quarantined (not imported by the main theorem) and labeled as scaffolding.
- **Always keep the project building**: after each meaningful change, run `lake build`.
- **No scope creep**: this plan is about *logical soundness and faithful interfaces*, not about proving RH unconditionally.

### How the assistant should operate (when given this file as prompt)
- **Workflow**:
  - Read the current state of the repo.
  - Find the first unchecked checkbox below.
  - Implement that step completely.
  - Mark it checked in this file.
  - Run `lake build`.
  - Make a git commit with a short message (unless the step explicitly says “no commit”).
  - Repeat.
- **When to stop**: only stop when the “Definition of done” at the bottom is met.

### Definitions
- **Classical analysis axiom (allowed)**: a statement that is expected to be true in standard mathematical analysis (e.g. Fefferman–Stein BMO→Carleson embedding) even if it’s hard to formalize.
- **Inconsistent axiom (not allowed)**: a statement that contradicts basic theorems already in Mathlib / standard analysis (e.g. a uniform bound on `∫` for *all* integrands on positive-length intervals).
- **Main chain**: everything imported (directly or indirectly) by `RiemannRecognitionGeometry/Main.lean`.

---

## Milestone 0 — Inventory + guardrails

- [x] **0.1 Record the current axiom surface.**
  - Produce a list of all `axiom` declarations in `RiemannRecognitionGeometry/`.
  - Partition them into:
    - **Allowed classical analysis axioms** (keep)
    - **Engineering/structure axioms** (dyadic / CZ bookkeeping; keep)
    - **Suspect axioms** (might be inconsistent; must be audited)
  - Save the result into this file under “Axiom registry” (append-only).

- [x] **0.2 Identify the main chain precisely.**
  - Starting from `RiemannRecognitionGeometry.lean` and `RiemannRecognitionGeometry/Main.lean`, list the modules imported in the transitive closure.
  - Confirm which axioms are actually in the main chain.
  - Add a short table to this file: **axiom → file → in main chain?**

- [x] **0.3 Add a repo rule: all axioms live in one place.**
  - Create `RiemannRecognitionGeometry/Conjectures.lean`.
  - Move all axioms that are meant to be “classical analysis assumptions” into that file.
  - Re-export them from the existing files (thin wrappers) so downstream code doesn’t break.
  - Goal: future audits are one-file.

---

## Milestone 1 — Remove inconsistent axioms (hard requirement)

### Known inconsistent module (historical): `RiemannRecognitionGeometry/FeffermanSteinBMO.lean`
This module was **deleted** (it contained “uniform bound for arbitrary integrands” style axioms).

The replacement interface is **scale-correct**:
- introduce `InBMOWithBound f M`
- define `K_tail(M) := C_FS * M^2` and `U_tail(M) := C_geom * sqrt(K_tail(M))`
- all Green/Fefferman–Stein/tail bounds now produce `U_tail(M)` (so no fixed universal `U_tail` can be derived from a mere `∃ M`)

- [x] **1.1 Decide: delete or repair `FeffermanSteinBMO.lean`.**
  - Preferred: **delete** it if it is not used anywhere in the main chain.
  - If it must remain, **repair** it by:
    - Redefining `tail_energy` to depend on the boundary function `f` (or its Poisson extension), not a constant.
    - Replacing `tail_pairing_bound_axiom` with a properly-scoped statement whose hypotheses imply the bound (e.g. assuming a Carleson energy bound and a normalized window test function).

- [x] **1.2 Enforce “no inconsistent axioms in build graph”.**
  - Make sure `lake build` does not compile any module that contains an inconsistent axiom.
  - If Lake builds all modules under the library by default, you must delete/repair the file rather than merely avoiding imports.

- [x] **1.3 Add a “consistency smoke test” module.**
  - Create `RiemannRecognitionGeometry/ConsistencySmokeTest.lean`.
  - Prove easy facts that would *immediately* refute the old inconsistent axioms, e.g.
    - For any positive-length interval, `|∫ t in Icc a b, (1:ℝ)| = b-a`.
    - Instantiate with a Whitney interval’s `interval` to show large integrals exist.
  - This module should compile and should not assume any project axioms.
  - Purpose: prevent reintroducing “uniform bound on all integrands”-type axioms.

---

## Milestone 2 — Make the project’s claims internally honest

- [x] **2.1 Fix “UNCONDITIONAL” labeling.**
  - Theorems now take an explicit oscillation certificate, either:
    - `(M : ℝ) (h_osc : InBMOWithBound logAbsXi M) (hM_le : M ≤ C_tail)`, or
    - the packaged proposition `OscillationTarget := ∃ M, InBMOWithBound logAbsXi M ∧ M ≤ C_tail`.
  - Docstrings/comments must state: **RH is proved conditional on this explicit small-oscillation hypothesis.**

- [x] **2.2 Separate “classical assumption” from “RG-specific conjecture”.**
  - Create a single bundled hypothesis structure, e.g.
    - `structure ClassicalAnalysisAssumptions` (Fefferman–Stein, Green identity, η/ζ identity principle, etc.)
    - `structure RGAssumptions` (the actual bottleneck estimate(s), if any)
  - Rewrite the main theorem signatures to depend on these structures rather than many loose axioms.

---

## Milestone 3 — Fix the phase object (faithfulness requirement)

Right now the main chain uses principal `Complex.arg` on ξ and treats it like a continuous harmonic conjugate. This mismatch makes the “FTC / Green / Cauchy–Riemann” story **not about the defined objects**.

- [x] **3.1 Introduce a faithful phase interface.**
  - Create `RiemannRecognitionGeometry/Phase.lean`.
  - Define a phase-change quantity that matches analysis, e.g. one of:
    - (Preferred) boundary value of the harmonic conjugate (via conjugate Poisson integral / Hilbert transform),
    - or an integral of `Im (ξ'/ξ)` along the critical line away from zeros.
  - Keep the old `argXi` only as a convenience, but stop using it in theorems that claim analytic identities.

- [x] **3.2 Refactor `actualPhaseSignal` and downstream lemmas to use the new phase.**
  - Update `RiemannRecognitionGeometry/FeffermanStein.lean` and `RiemannRecognitionGeometry/Axioms.lean` so the “phase bound” theorems/axioms are stated for the new phase object.

- [x] **3.3 Add explicit “branch / continuity” hypotheses where needed.**
  - Any statement using a phase difference should either:
    - assume ξ is nonzero on the interval (so a continuous argument lift exists), or
    - work with winding number / `Real.Angle`, then lift.

---

## Milestone 4 — Quarantine or remove scaffolding definitions

- [x] **4.1 Quarantine `BMOCarleson.lean` if it remains definitional scaffolding.**
  - `phaseIntegral := U_tail/3` is not a real integral.
  - Either:
    - remove the module from the library build / imports, or
    - rewrite it to define the genuine integral and prove the bound from the axioms.

- [x] **4.2 Eliminate “proof-by-definition” from anything imported by `Main.lean`.**
  - Search for definitions that hard-code desired bounds and ensure they are not used in the main chain.

---

## Milestone 5 — Tighten the axiom statements (make them plausibly true)

- [x] **5.1 Rewrite any axiom that is too broad.**
  - Rule: if the axiom quantifies over *all* functions/integrands and returns a uniform numerical bound independent of the input, it is almost certainly inconsistent.
  - Replace such axioms with statements whose conclusions scale correctly (e.g. depend on norms and interval length).

- [x] **5.2 Add “unit tests” for each axiom family.**
  - For each axiom about integrals/inequalities, add a small lemma file showing it behaves correctly on:
    - `f := 0`, `f := 1`, indicator functions, etc.
  - These are not mathematical proofs of the axiom; they are checks that the formulation isn’t *obviously* contradictory.

---

## Axiom registry (append-only)

### Snapshot (2025-12-12)

Total `axiom` declarations in `RiemannRecognitionGeometry/`: **18**.

#### Allowed classical analysis axioms (keep)
- **`identity_principle_eta_zeta_lt_one_axiom`** — `RiemannRecognitionGeometry/DirichletEta.lean`
  (Identity principle / analytic continuation input for η–ζ relation on `0<s<1`.)
- **`bmo_carleson_embedding`** — `RiemannRecognitionGeometry/PoissonExtension.lean`
  (Fefferman–Stein BMO→Carleson embedding; classical harmonic analysis.)
- **`green_identity_axiom_statement`** — `RiemannRecognitionGeometry/Axioms.lean`
  (Green/Cauchy–Riemann/Cauchy–Schwarz phase bound; classical harmonic analysis.)
- **`weierstrass_tail_bound_axiom_statement`** — `RiemannRecognitionGeometry/Axioms.lean`
  (RG-specific “tail bound” / factorization estimate. Not a standard textbook axiom, but not obviously inconsistent.)
- **`zero_has_large_im`** — `RiemannRecognitionGeometry/Basic.lean`
  (Numerical input: first nontrivial zero height > 14; consistent with standard facts.)

#### Engineering / structure axioms (keep)
- **`whitney_len_from_strip_height_axiom`** — `RiemannRecognitionGeometry/Basic.lean`
  (Whitney covering geometry input for length lower bound.)
- **`whitney_centered_from_strip_axiom`** — `RiemannRecognitionGeometry/Basic.lean`
  (Whitney covering geometry input for centering.)
- **`dyadic_nesting`** — `RiemannRecognitionGeometry/JohnNirenberg.lean`
  (Dyadic grid nesting; bookkeeping/structure.)
- **`maximalBad_disjoint_axiom`** — `RiemannRecognitionGeometry/JohnNirenberg.lean`
  (Maximal-bad intervals disjointness; CZ bookkeeping.)
- **`DyadicInterval.avg_doubling_axiom`** — `RiemannRecognitionGeometry/JohnNirenberg.lean`
  (Dyadic doubling of averages; elementary measure/integral bookkeeping.)
- **`czDecomposition_axiom`** — `RiemannRecognitionGeometry/JohnNirenberg.lean`
  (Existence of dyadic CZ decomposition; classical but treated here as infrastructure.)
- **`czDecompFull_axiom`** — `RiemannRecognitionGeometry/JohnNirenberg.lean`
  (Full CZ decomposition with good/bad parts; infrastructure.)
- **`goodLambda_axiom`** — `RiemannRecognitionGeometry/JohnNirenberg.lean`
  (Good-λ step; infrastructure for JN/BMO consequences.)
- **`jn_first_step_axiom`** — `RiemannRecognitionGeometry/JohnNirenberg.lean`
  (First step in John–Nirenberg; infrastructure.)
- **`bmo_Lp_bound_axiom`** — `RiemannRecognitionGeometry/JohnNirenberg.lean`
  (BMO→Lᵖ control; infrastructure.)
- **`bmo_kernel_bound_axiom`** — `RiemannRecognitionGeometry/JohnNirenberg.lean`
  (Kernel bound used in harmonic analysis chain; infrastructure.)

#### Suspect axioms (must audit; likely inconsistent as currently formulated)
- **`fefferman_stein_bmo_carleson`** — `RiemannRecognitionGeometry/FeffermanSteinBMO.lean`
  **Suspect** because `tail_energy` in that file is defined as a constant multiple of `I.len` (independent of `f`), while the axiom quantifies over all `f` and all BMO bounds `M`.
- **`tail_pairing_bound_axiom`** — `RiemannRecognitionGeometry/FeffermanSteinBMO.lean`
  **Inconsistent** as stated: it bounds `|∫_I integrand|` by a fixed constant for *all* `integrand` on any positive-length interval.

#### Main chain import closure (project modules only)
Starting points:
- `RiemannRecognitionGeometry.lean`
- `RiemannRecognitionGeometry/Main.lean`

Project modules in the transitive import closure:
- `RiemannRecognitionGeometry.Mathlib.ArctanTwoGtOnePointOne`
- `RiemannRecognitionGeometry.Basic`
- `RiemannRecognitionGeometry.Axioms`
- `RiemannRecognitionGeometry.WhitneyGeometry`
- `RiemannRecognitionGeometry.PoissonJensen`
- `RiemannRecognitionGeometry.CarlesonBound`
- `RiemannRecognitionGeometry.FeffermanStein`
- `RiemannRecognitionGeometry.JohnNirenberg`
- `RiemannRecognitionGeometry.DirichletEta`
- `RiemannRecognitionGeometry.PoissonExtension`
- `RiemannRecognitionGeometry.FeffermanSteinBMO`  *(currently imported by `Axioms.lean`; this is the inconsistent module to remove/repair in Milestone 1)*
- `RiemannRecognitionGeometry.Main`

#### Axiom → file → in main chain?
All project axioms are currently in the main chain (via `RiemannRecognitionGeometry.lean` → `Axioms.lean` imports).

| axiom | file | in main chain? |
|---|---|---|
| `identity_principle_eta_zeta_lt_one_axiom` | `RiemannRecognitionGeometry/DirichletEta.lean` | ✅ yes |
| `dyadic_nesting` | `RiemannRecognitionGeometry/JohnNirenberg.lean` | ✅ yes |
| `maximalBad_disjoint_axiom` | `RiemannRecognitionGeometry/JohnNirenberg.lean` | ✅ yes |
| `DyadicInterval.avg_doubling_axiom` | `RiemannRecognitionGeometry/JohnNirenberg.lean` | ✅ yes |
| `czDecomposition_axiom` | `RiemannRecognitionGeometry/JohnNirenberg.lean` | ✅ yes |
| `czDecompFull_axiom` | `RiemannRecognitionGeometry/JohnNirenberg.lean` | ✅ yes |
| `goodLambda_axiom` | `RiemannRecognitionGeometry/JohnNirenberg.lean` | ✅ yes |
| `jn_first_step_axiom` | `RiemannRecognitionGeometry/JohnNirenberg.lean` | ✅ yes |
| `bmo_Lp_bound_axiom` | `RiemannRecognitionGeometry/JohnNirenberg.lean` | ✅ yes |
| `bmo_kernel_bound_axiom` | `RiemannRecognitionGeometry/JohnNirenberg.lean` | ✅ yes |
| `zero_has_large_im` | `RiemannRecognitionGeometry/Basic.lean` | ✅ yes |
| `whitney_len_from_strip_height_axiom` | `RiemannRecognitionGeometry/Basic.lean` | ✅ yes |
| `whitney_centered_from_strip_axiom` | `RiemannRecognitionGeometry/Basic.lean` | ✅ yes |
| `fefferman_stein_bmo_carleson` | `RiemannRecognitionGeometry/FeffermanSteinBMO.lean` | ✅ yes *(problematic)* |
| `tail_pairing_bound_axiom` | `RiemannRecognitionGeometry/FeffermanSteinBMO.lean` | ✅ yes *(problematic)* |
| `bmo_carleson_embedding` | `RiemannRecognitionGeometry/PoissonExtension.lean` | ✅ yes |
| `green_identity_axiom_statement` | `RiemannRecognitionGeometry/Axioms.lean` | ✅ yes |
| `weierstrass_tail_bound_axiom_statement` | `RiemannRecognitionGeometry/Axioms.lean` | ✅ yes |

#### Update (2025-12-12): assumptions bundled; `Conjectures.lean` now exports wrappers
- `RiemannRecognitionGeometry/Assumptions.lean` defines the two bundled assumption structures:
  - `ClassicalAnalysisAssumptions.green_identity_axiom_statement`
  - `RGAssumptions.weierstrass_tail_bound_axiom_statement`
- `RiemannRecognitionGeometry/Conjectures.lean` now provides **theorem wrappers** (no `axiom` declarations):
  - `Conjectures.green_identity_axiom_statement (hCA : ClassicalAnalysisAssumptions) ...`
  - `Conjectures.weierstrass_tail_bound_axiom_statement (hRG : RGAssumptions) ...`
- `RiemannRecognitionGeometry/Axioms.lean` also provides wrappers (for backward compatibility) used by the main chain.

Corrected assumption locations:

| assumption | file | in main chain? |
|---|---|---|
| `ClassicalAnalysisAssumptions.green_identity_axiom_statement` | `RiemannRecognitionGeometry/Assumptions.lean` | ✅ yes |
| `RGAssumptions.weierstrass_tail_bound_axiom_statement` | `RiemannRecognitionGeometry/Assumptions.lean` | ✅ yes |

#### Update (2025-12-12): inconsistent axioms removed from build graph
- Deleted the inconsistent module `RiemannRecognitionGeometry/FeffermanSteinBMO.lean` and removed its import from `RiemannRecognitionGeometry/Axioms.lean`.
- Also reduced the axiom surface:
  - Removed `zero_has_large_im`, `whitney_len_from_strip_height_axiom`, `whitney_centered_from_strip_axiom` (Basic.lean now has 0 axioms).
  - Proved `dyadic_nesting` and `DyadicInterval.avg_doubling` as theorems (removed axioms).
  - Removed the incorrect/unneeded `maximalBad_disjoint_axiom`.
  - JohnNirenberg CZ surface is now 6 axioms.

Updated main-chain import closure (high-level):
- `RiemannRecognitionGeometry.Mathlib.ArctanTwoGtOnePointOne`
- `RiemannRecognitionGeometry.Basic`
- `RiemannRecognitionGeometry.Axioms` (imports `Conjectures`, `JohnNirenberg`, `DirichletEta`, `PoissonExtension`)
- `RiemannRecognitionGeometry.WhitneyGeometry`
- `RiemannRecognitionGeometry.PoissonJensen`
- `RiemannRecognitionGeometry.CarlesonBound`
- `RiemannRecognitionGeometry.FeffermanStein`
- `RiemannRecognitionGeometry.Main`

Updated assumption surface (all in main chain; total = 10):

| assumption | file | in main chain? |
|---|---|---|
| `ClassicalAnalysisAssumptions.green_identity_axiom_statement` | `RiemannRecognitionGeometry/Assumptions.lean` | ✅ yes |
| `RGAssumptions.weierstrass_tail_bound_axiom_statement` | `RiemannRecognitionGeometry/Assumptions.lean` | ✅ yes |
| `identity_principle_eta_zeta_lt_one_axiom` | `RiemannRecognitionGeometry/DirichletEta.lean` | ✅ yes |
| `czDecomposition_axiom` | `RiemannRecognitionGeometry/JohnNirenberg.lean` | ✅ yes |
| `czDecompFull_axiom` | `RiemannRecognitionGeometry/JohnNirenberg.lean` | ✅ yes |
| `goodLambda_axiom` | `RiemannRecognitionGeometry/JohnNirenberg.lean` | ✅ yes |
| `jn_first_step_axiom` | `RiemannRecognitionGeometry/JohnNirenberg.lean` | ✅ yes |
| `bmo_Lp_bound_axiom` | `RiemannRecognitionGeometry/JohnNirenberg.lean` | ✅ yes |
| `bmo_kernel_bound_axiom` | `RiemannRecognitionGeometry/JohnNirenberg.lean` | ✅ yes |
| `bmo_carleson_embedding` | `RiemannRecognitionGeometry/PoissonExtension.lean` | ✅ yes |

---

## Definition of done

All of the following must be true:
- **(D1)** `lake build` succeeds.
- **(D2)** There are **no inconsistent axioms in any compiled module** (especially no “uniform bound for arbitrary integrands” style axioms).
- **(D3)** The main theorem(s) and docs honestly state all remaining hypotheses (e.g. `OscillationTarget` / `InBMOWithBound logAbsXi M ∧ M ≤ C_tail`), and “UNCONDITIONAL” is not claimed unless the hypothesis is actually removed.
- **(D4)** Phase-related results are stated about a phase object that matches the analytic machinery (continuous lift / harmonic conjugate / log-derivative integral), not principal `Complex.arg`.
