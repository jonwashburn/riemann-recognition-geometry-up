## Route 3 execution plan (Weil explicit formula / Li positivity)

This plan is meant to be executed **top-to-bottom**. Always work on the **first unchecked checkbox**, keep the repo building, and only move forward when the acceptance criteria for the current checkbox are met.

### Goal (Route 3)

Produce a **self-contained, citation-correct, mechanically checkable proof skeleton** in which the *only* remaining bottleneck for RH is an **explicit-formula positivity statement**:

- **Weil gate**: prove Weil positivity \(W^{(1)}(f*\widetilde{\overline f})\ge 0\) for all admissible test functions \(f\).
- **Li gate**: prove Li positivity \(\lambda_n\ge 0\) for all \(n\ge 1\).

Route 3 must be **logically and code-wise separated** from the current BMO/Carleson/Whitney infrastructure (which may be referenced only for comparison/deprecation).

### Non-negotiable constraints

- **Keep the repo building**:
  - After meaningful Lean changes: `lake build`
  - After meaningful TeX changes: `pdflatex` compile (twice) for `CPM.tex` and `recognition-geometry-dec-12-new-route.tex`
- **No accidental dependency on the old route**: Route 3 Lean modules must not import `CarlesonBound`, `FeffermanStein`, `WhitneyGeometry`, etc.
- **No inconsistent axioms**: any axioms introduced must be standard/plausible (no “uniform bound for all integrands on all intervals” style statements).
- **Notation lock**: use Lagarias’ normalization consistently (see `renormalized_tail_bound.md` §8).

---

## Milestone 0 — Documentation baseline (DONE)

- [x] Strengthen `renormalized_tail_bound.md` §8 with Lagarias normalization, explicit formula, Weil positivity, Li criterion, Conrey–Li warning, and “what would close the proof”.
- [x] Add CPM framing paragraph + bibliography for Lagarias/Li/Bombieri–Lagarias/Conrey–Li/Weil in `CPM.tex`.
- [x] Align the Route 3 addendum bullet in `recognition-geometry-dec-12-new-route.tex`.
- [x] Confirm `pdflatex` builds succeed for `CPM.tex` and `recognition-geometry-dec-12-new-route.tex`.

Acceptance criteria:
- `pdflatex` succeeds (twice) on both TeX files.
- `renormalized_tail_bound.md` §8 is self-contained and citation-correct.

---

## Milestone 1 — Lock the Route 3 “gate” interface (Weil primary, Li secondary)

We will treat **Weil positivity** as the primary gate (universal quantifier, matches CPM quadratic-form language), and treat **Li positivity** as a countable specialization.

- [x] **1.1 Create a Route 3 Lean namespace that does not import the old route.**
  - Add new module(s) under `RiemannRecognitionGeometry/ExplicitFormula/`:
    - `Defs.lean` (test functions + Mellin/convolution/involution interfaces)
    - `Lagarias.lean` (explicit formula + Weil criterion statements)
    - `Li.lean` (Li coefficients + criterion + link to Weil)
    - `MainRoute3.lean` (the “gate → RH” theorems)

Acceptance criteria:
- `lake build` succeeds.
- `RiemannRecognitionGeometry/ExplicitFormula/MainRoute3.lean` compiles while importing **only** Mathlib essentials + the new Route 3 modules.

---

## Milestone 2 — Formalize the minimal Route 3 objects (Lean)

The point here is *mechanical checkability*, not rebuilding analytic number theory inside Lean immediately. Start with a **minimal interface** whose axioms are explicitly labeled and whose statements match Lagarias.

- [x] **2.1 Define Lagarias’ \(\xi\) in Lean (or wrap Mathlib’s objects).**
  - Define `xiLagarias : ℂ → ℂ` by \(\xi(s)=\tfrac12 s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s)\).
  - Prove (or assume, clearly) basic facts needed for statements:
    - `xiLagarias (1 - s) = xiLagarias s`
    - zeros of `xiLagarias` correspond to nontrivial zeros of `riemannZeta`

- [x] **2.2 Define the test-function operations.**
  Implement either:
  - (Preferred) actual definitions using integrals over \((0,\infty)\) with measure `dx/x`, or
  - (Fast skeleton) an abstract `structure NiceTestFunction` with operations `Mellin`, `conv`, `tilde` plus axioms:
    - `Mellin (f * g) = Mellin f * Mellin g`
    - `Mellin (tilde f) (s) = Mellin f (1 - s)`

- [x] **2.3 Define the explicit-formula functionals.**
  Define `W2(f)=M[f](1)`, `W0(f)=M[f](0)`, and a *formal* `W1(f)=∑_ρ M[f](ρ)` with an explicit convergence convention (symmetric summation).
  Define `Wspec(f)=W2(f)-W1(f)+W0(f)` and `Warith(f)` (prime powers + archimedean term).

Acceptance criteria:
- The definitions compile in Lean.
- Any nontrivial analytic convergence claims are either proven or clearly marked as assumptions in a dedicated “assumptions” structure for Route 3.

---

## Milestone 3 — State Lagarias Theorems as Lean theorems/axioms (mechanical skeleton)

- [x] **3.1 Explicit formula (Lagarias Thm 3.1).**
  Add a theorem/axiom in `ExplicitFormula/Lagarias.lean` matching:
  \(W_{\mathrm{spec}}(f)=W_{\mathrm{arith}}(f)\) for all “nice” test functions.

- [x] **3.2 Weil positivity (Lagarias Thm 3.2).**
  Add a theorem/axiom matching:
  \(\mathrm{RH}\iff W^{(1)}(f*\widetilde{\overline f})\ge 0\) for all “nice” \(f\).

Acceptance criteria:
- In Lean, the statements are *typed*, *named*, and match the prose in `renormalized_tail_bound.md` §8.
- Route 3 theorems do **not** depend on the old route’s assumptions (`OscillationTarget`, Carleson bounds, etc.).

---

## Milestone 4 — Produce the Route 3 “gate → RH” theorem(s) (Lean)

- [x] **4.1 Weil gate theorem.**
  Prove a theorem of the form:

  - `WeilGate → RiemannHypothesis`  *(Mathlib’s formal RH predicate)*

  where `WeilGate` is exactly the positivity hypothesis
  \(\forall f,\ W^{(1)}(f*\widetilde{\overline f})\ge 0\) on the chosen test class.

- [x] **4.2 Conrey–Li warning encoded as a “non-goal”.**
  Add a short comment (and optionally a stub lemma) in Route 3 docs/Lean noting that de Branges shift-positivity is **not** the target (Conrey–Li counterexamples).

Acceptance criteria:
- `lake build` succeeds.
- There is a single “Route 3 main theorem” file (`MainRoute3.lean`) whose only substantive remaining hypothesis is the Weil gate.

---

## Milestone 5 — Li gate (countable specialization) and its link to Weil

- [x] **5.1 Define Li coefficients \(\lambda_n\)** as in Lagarias §6.3.
- [x] **5.2 State Li criterion (Lagarias Thm 6.5).**
- [x] **5.3 Add the symmetric “sum over zeros” formula** with a stated convergence convention.
- [x] **5.4 Record the Bombieri–Lagarias/Lagarias link** \(\lambda_n=W^{(1)}(\phi_n*\widetilde{\overline{\phi_n}})\) with an explicit test-class caveat.

Acceptance criteria:
- Lean has a `LiGate → RH` theorem (even if it relies on a packaged theorem/axiom matching Lagarias).

---

## Milestone 6 — Optional: make the bottleneck feel “attackable”

These do **not** change the core bottleneck, but turn it into concrete subtargets.

- [x] **6.1 Dense-subclass reduction lemma (Weil).**
  Prove (or state precisely as a target) a continuity statement implying it suffices to check positivity on a dense subclass (e.g. smooth compactly supported tests).

- [x] **6.2 Eventual positivity program (Li).**
  Derive (or target) a prime-power explicit formula for \(\lambda_n\) with a remainder bound strong enough to imply \(\lambda_n>0\) for all \(n\ge N_0\), reducing RH to finitely many checks.

Acceptance criteria:
- These are stated in a way that could be independently attacked, without importing the old route.

---

## Definition of done

All of the following must be true:

- **(D1)** `pdflatex` (twice) succeeds for `CPM.tex` and `recognition-geometry-dec-12-new-route.tex`.
- **(D2)** `lake build` succeeds.
- **(D3)** There exists a Route 3 Lean theorem `WeilGate → RiemannHypothesis` (and optionally `LiGate → ...`) whose hypotheses do **not** include the old Carleson/BMO machinery.
- **(D4)** The repo clearly identifies the **sole remaining bottleneck** as explicit-formula positivity (Weil or Li), with Conrey–Li’s “shift positivity fails” warning prominently preserved.
