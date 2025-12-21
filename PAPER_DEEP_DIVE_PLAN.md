### Paper Deep-Dive Plan (2025-12-20)

This document is a **working plan** for doing a deep dive on the **most relevant recent papers** we found and mapping them to the **exact blockers** in:

- the written proof: `recognition-geometry-dec-18.tex`
- the Lean development: `RiemannRecognitionGeometry/`

The goal is not “read everything”; it’s: **extract the smallest set of results that can discharge one of the typed proof-holes** (or convincingly rule out a direction).

---

### 0) The blockers we’re trying to move

#### Route 3 (explicit formula / Weil–Li)
- **Primary target (measure-first)**: produce a `SesqMeasureIntegralIdentity` / `SesqMeasureIdentity` for the Weil pairing:
  - **Lean interface**: `RiemannRecognitionGeometry/ExplicitFormula/HilbertRealization.lean`  
    - `SesqMeasureIntegralIdentity.identity_integral`
    - `SesqMeasureIdentity.identity`
  - **Driver packaging**: `RiemannRecognitionGeometry/ExplicitFormula/PSCSplice.lean`  
    - `Route3.PSCSplice.IntegralAssumptions.identity_integral`
  - **Strategy packaging**: `RiemannRecognitionGeometry/ExplicitFormula/CayleyBridge.lean`  
    - `CayleyMeasureBridgeAssumptions.bridge_to_measure` (preferred)
    - `CayleyBridgeAssumptions.bridge_to_reflection` (stronger)

#### RG / boundary-certificate track
- **B1**: energy ⇒ phase control (Green/CR/trace/FTC gates).
  - **Lean interface**: `RiemannRecognitionGeometry/Assumptions.lean`
    - `ClassicalAnalysisAssumptions.cofactor_green_identity_axiom_statement`
    - `RGAssumptions.j_carleson_energy_axiom_statement`
- **B2′**: renormalized/local tail oscillation certificate (or μ-Carleson ⇒ B2′).
  - **Lean interface**: `RiemannRecognitionGeometry/OscillationTargetTail.lean`
    - `OscillationTargetTail`
    - `oscillationTargetTail_of_muCarleson` (axiomatized)

---

### 1) Deep-dive workflow (repeatable for each paper)

#### 1.1 Deliverables per paper (lightweight but structured)
For each paper, create a notes file under a new folder `notes/papers/` (or keep in root if you prefer):

- **File**: `notes/papers/<arxiv-id>-notes.md`
- **Sections** (copy/paste template below):
  - **Citation** (authors, title, arXiv/DOI, date)
  - **What the paper *actually proves*** (1–5 bullet theorem statements)
  - **Assumptions** (explicit dependence on RH/GRH, zero-free regions, etc.)
  - **Constants** (explicit vs implicit; where the constants live)
  - **Mapping to our objects**
    - Map their quantities to our `μ`, Carleson boxes `Q(I)`, Whitney scale `L`, etc.
    - Map their “test functions” to our Route‑3 `TestSpace` semantics if relevant.
  - **Which blocker it could discharge**
  - **What would still be missing**
  - **Actionable extraction** (what to cite, what to formalize, what to treat as external theorem)

#### 1.2 Template: paper notes skeleton

```markdown
### <Title> (<arXiv-id>)

- **Citation**:
- **One-line relevance**:

#### Results to extract
- **R1**:
- **R2**:

#### Assumptions / caveats
- **A1**:

#### Constants
- **Explicit?**:
- **Depends on**:

#### Mapping to our framework
- **Maps to**:
  - `μ`:
  - `Q(I)`:
  - `OscillationTargetTail`:
  - `PSCSplice` / `SesqMeasureIdentity`:

#### Can it discharge a blocker?
- **Best case**:
- **Worst case**:

#### Next actions
- **Extract**:
- **Try to derive**:
- **If it fails, why**:
```

#### 1.3 Translation checklist (for number theory → μ-Carleson)
When a paper gives a density estimate of the form \(N(\sigma,T)\) bounds:

- **Goal**: bound the σ-weighted off-line measure in a Carleson box:
  - \( \mu(Q(I)) = \sum_{\rho \in Q(I),\,\Re\rho>1/2}(\Re\rho-1/2)\)
- **Standard conversion** (to attempt):
  - Use the identity:
    \[
      \sum_{\rho \in \mathcal{R}} (\beta_\rho - 1/2)
      \;=\;
      \int_{1/2}^{1} N_{\mathcal{R}}(\sigma)\, d\sigma
    \]
    where \(N_{\mathcal{R}}(\sigma)\) counts zeros in the region with \(\beta_\rho \ge \sigma\).
  - Then apply the paper’s bound on \(N(\sigma,T)\) in the relevant \(T\)-window matching the horizontal width of \(Q(I)\).
- **Reality check**: most density results are global in \(T\), so you must also bound the number of zeros in a *short interval* in height; if the paper doesn’t provide that, you’ll need a standard “localization” lemma (e.g. by monotonicity + covering argument).

#### 1.4 Translation checklist (for Route 3: positivity/kernel → \(L^2(\mu)\))
When a paper reframes Li/Weil positivity as a norm or positive kernel:

- **Goal**: a statement of the form
  \[
  W^{(1)}(\mathrm{pair}(f,g)) \;=\; \int \overline{F_f}\,F_g\, d\mu
  \]
  or an equivalent RKHS/Hilbert model.
- **Lean target**: fill `SesqMeasureIntegralIdentity.identity_integral` (best) or
  `CayleyMeasureBridgeAssumptions.bridge_to_measure` (still huge, but typed).
- **What to extract**:
  - The exact Hilbert space / model space.
  - The precise transform \(f \mapsto F_f\).
  - Identification of the measure \(d\mu\) (Clark measure / spectral measure).
  - Any equivalence “RH ⇔ the function is inner / the measure is positive”.

---

### 2) Paper-by-paper dive plan (current shortlist)

### 2.0 Deep-dive status (completed) + where the results live

Deep dives are now written up here:

- **Summary map (paper → blocker → Lean touchpoint)**: `notes/papers/DEEP_DIVE_SUMMARY.md`
- **Per-paper notes**:
  - `notes/papers/2405.12545-bellotti-notes.md`
  - `notes/papers/2501.16779-tao-trudgian-yang-notes.md`
  - `notes/papers/2405.20552-guth-maynard-notes.md`
  - `notes/papers/2403.13157-matomaki-teravainen-notes.md`
  - `notes/papers/2310.04544-pintz-notes.md`
  - `notes/papers/2301.05779-suzuki-notes.md`
  - `notes/papers/2301.00421-suzuki-weil-distribution-notes.md`
  - `notes/papers/2311.08519-weil-spectral-measures-notes.md`
  - `notes/papers/2409.00888-matsumoto-suzuki-notes.md`
  - `notes/papers/2412.02068-chourasiya-notes.md`
  - `notes/papers/2206.11729-maynard-pratt-notes.md`
  - `notes/papers/2206.03682-screw-function-aspects-notes.md`
  - `notes/papers/2310.18423-prolate-wave-operators-notes.md`
  - `notes/papers/2112.05500-prolate-spheroidal-operator-zeta-notes.md`
  - `notes/papers/2402.13082-heat-expansion-zeta-notes.md`
  - `notes/papers/2511.22755-zeta-spectral-triples-notes.md`
  - `notes/papers/2511.23257-quadratic-forms-real-zeros-notes.md`
  - `notes/papers/2106.01715-spectral-triples-zeta-cycles-notes.md`
  - `notes/papers/2207.10419-hochschild-trace-zeta-cycles-notes.md`
  - `notes/papers/2104.09899-cyclic-cocycles-spectral-action-notes.md`
  - `notes/papers/2511.07495-selector-kernels-fredholm-notes.md`
  - `notes/papers/2301.00421-suzuki-weil-distribution-notes.md`
  - `notes/papers/2311.08519-weil-spectral-measures-notes.md`
  - `notes/papers/2409.00888-matsumoto-suzuki-notes.md`

**Bottom line**:

- **B2′ / μ‑Carleson**: these papers mostly help with **far-right regimes** (\(\Re\rho\) bounded away from \(1/2\)), but do *not* directly imply the **uniform local** `MuCarleson` predicate we need in Lean (`RiemannRecognitionGeometry/MuCarleson.lean`).
- **Route 3**: Suzuki is the most relevant conceptually; it reframes Li coefficients as \(L^2\)-norms in a model-space picture, but the key identity remains **RH-equivalent** (so it shapes targets more than it closes the splice gap).

### 2.0.1 Lean integration points (what we added/changed to reflect the deep dives)

These are small, typed “bridge targets” so the papers can actually influence the Lean proof architecture:

- **Route 3 / Suzuki (Li-as-\(L^2\)-norm)**: `RiemannRecognitionGeometry/ExplicitFormula/SuzukiBridge.lean`
- **Route 3 / Matsumoto–Suzuki (screw-function kernel positivity)**: `RiemannRecognitionGeometry/ExplicitFormula/ScrewFunctionBridge.lean`
- **Route 3 / spectral-measure operator route (arXiv:2311.08519 shape)**: `RiemannRecognitionGeometry/ExplicitFormula/OperatorSpectralMeasureBridge.lean`
  - now includes **sesquilinear** targets too: `OperatorSesqIdentity` and `SpectralMeasureSesqIntegralIdentity`
  - and it is now a **drop‑in Route‑3 target**: `SpectralMeasureSesqIntegralIdentity.reflectionPositivityRealization` yields `OptionalTargets.ReflectionPositivityRealization` via the existing `HilbertRealization` pipeline
- **Route 3′ / Connes determinant-approximant gate (Hurwitz step packaged)**:
  - `RiemannRecognitionGeometry/ExplicitFormula/HurwitzGate.lean` (`HurwitzOffRealAxisInStripGate`)
  - `RiemannRecognitionGeometry/ExplicitFormula/ConnesHurwitzBridge.lean` (packages the assumptions as `ConnesHurwitzAssumptions` and exposes a single `RiemannHypothesis` target)
  - `RiemannRecognitionGeometry/ExplicitFormula/ConnesConvergenceBundle.lean` (typed surface for the Section 8 “missing steps”)
    - `ConnesMissingStepSimpleEven` (M1: ground state exists / even / simple, normalized by `ξ_λ(λ)=1`)
    - `ConnesMissingStep_kλ_approximates_ξλ` (M2: uniform-on-`[λ⁻¹,λ]` approximation `k_λ ≈ c_λ ξ_λ` with error → 0)
  - `RiemannRecognitionGeometry/ExplicitFormula/RealZeros.lean` (glue: “all zeros real” ⇒ the `HurwitzGate` zero-free hypotheses on upper/lower strip)
- **RG B2′ / μ-Carleson near/far split scaffold**:
  - `RiemannRecognitionGeometry/MuCarlesonOps.lean`
  - `RiemannRecognitionGeometry/AssumptionsTail.lean` (`MuCarlesonSplitAssumptions`)
  - `RiemannRecognitionGeometry/ZeroDensityAssumptions.lean` (stub: literature-style zero density ⇒ far μ‑Carleson, designed to pair with the Tao–Trudgian–Yang “energy ⇒ near μ‑Carleson” scaffold)

#### 2.0.2 Far-regime “δ thresholds” (what the literature can plausibly cover)

In Lean we store off-critical zeros as points \((t,\sigma')=(\gamma,\beta-\tfrac12)\). A natural near/far split is:

- **near**: `sigmaLeSet δ = {σ' ≤ δ}`
- **far**: `(sigmaLeSet δ)ᶜ = {σ' > δ}`.

The papers we deep-dived support **far** control only for *fixed* δ bounded away from 0:

- **Chourasiya `2412.02068`**:
  - **σ-range**: \(\beta\ge 0.6\) i.e. \(\sigma'=\beta-\tfrac12 \ge 0.1\) (**δ = 0.1**)
  - **Form**: explicit Carlson-type \(N(\sigma,T)\le K(\sigma,T_0)T^{4\sigma(1-\sigma)}(\log T)^{5-2\sigma}\) for \(T\ge 3\cdot 10^{12}\).
  - **Use**: plausible provider for the “far μ‑Carleson” half of the split (as an external lemma/assumption).
  - **Note**: the restriction \(T\ge 3\cdot 10^{12}\) is consistent with the standard computational “RH verified up to \(3\cdot10^{12}\)” barrier used in explicit-density papers; below that height one treats the range separately (finite check) in explicit-constant arguments.

- **Bellotti `2405.12545` (uniform specialization)**:
  - **σ-range**: \(\beta\ge 0.9927\) i.e. \(\sigma'\ge 0.4927\) (**δ ≈ 0.4927**)
  - **Form**: explicit log-free \(N(\sigma,T)\le C\,T^{1.448(1-\sigma)}\) in a huge explicit \(T\)-range.
  - **Use**: rules out *very* far-right zeros as the obstruction, but δ is so large it doesn’t meaningfully shrink the hard near regime.

Rule of thumb:
- If you want a **useful split** that actually shrinks the hard regime, start with **δ = 0.1** (Chourasiya).
- Anything much smaller than that currently needs new “near-critical” structure/energy input (not raw density).

#### 2.1 Chiara Bellotti — `arXiv:2405.12545`
**Title**: “An explicit log-free zero density estimate for the Riemann zeta-function”

- **Target blocker**: RG **B2′** via a concrete Carleson/packing bound for the off-line zero measure `μ`.
- **Deep-dive focus**:
  - Extract the strongest usable bound in the form: \(N(\sigma,T) \le C(\sigma)\,T^{a(\sigma)}\) with explicit constants.
  - Determine if it’s already “local enough” or if we need a localization lemma.
- **Mapping tasks**:
  - Translate their bound into a bound on \(\mu(Q(I))\) with \(Q(I)\) matching your `inLocalWindow` geometry (cf. `OscillationTargetTail.lean`’s `dilatedWhitney`).
  - Identify whether the bound is strong enough to yield geometric decay in `K` (the dyadic cutoff).
- **Success criterion**:
  - Produce a credible route to implementing (or justifying as an external lemma)  
    `oscillationTargetTail_of_muCarleson` in `RiemannRecognitionGeometry/OscillationTargetTail.lean`.

- **Deep-dive verdict**: helpful as **support** for ruling out “very far-right zeros” as the obstruction, but **not** a direct path to `MuCarleson` / `OscillationTargetTail`.  
  See `notes/papers/2405.12545-bellotti-notes.md`.

#### 2.2 Tao–Trudgian–Yang — `arXiv:2501.16779`
**Title**: “New exponent pairs, zero density estimates, and zero additive energy estimates: a systematic approach”

- **Target blocker**: RG **B2′** (same funnel), but aiming for stronger exponents/structure.
- **Deep-dive focus**:
  - Identify the “off-the-shelf” zero-density corollaries and their ranges.
  - Check if the paper provides *explicit* constants; if not, assess whether it can still be used as a “citable external theorem” for the written proof.
- **Mapping tasks**:
  - Same conversion \(N(\sigma,T)\to \mu(Q(I))\).
  - See if any “additive energy” bounds can be interpreted as a packing statement that is closer to Carleson geometry than classical density bounds.
- **Success criterion**:
  - A clean lemma statement to cite in the written proof that implies the needed Carleson packing bound for μ.

- **Deep-dive verdict**: high-value strategically (especially **additive energy** of zeros), but not plug-and-play for Lean’s `MuCarleson` without an additional “local-to-Whitney-window” bridge lemma.  
  See `notes/papers/2501.16779-tao-trudgian-yang-notes.md`.

#### 2.3 Matomäki–Teräväinen — `arXiv:2403.13157`
**Title**: “A note on zero density results implying large value estimates for Dirichlet polynomials”

- **Target blocker**: RG **B2′** (via “large values ↔ zeros” mechanisms).
- **Deep-dive focus**:
  - Identify the exact direction proved: does a zero-density hypothesis control large values, or conversely?
  - Look for a “local” variant that controls large values on intervals comparable to Whitney intervals.
- **Mapping tasks**:
  - If it controls large values of Dirichlet polynomials approximating \(\log \zeta\), see if that implies localized BMO control of the renormalized tail.
- **Success criterion**:
  - A realistic route from large-value control to `InBMOWithBoundOnWhitney (tailLogAbs ...)`.

- **Deep-dive verdict**: gives a useful **reduction mechanism** (zero density ⇒ large values), but doesn’t itself discharge any current Lean axiom/hole.  
  See `notes/papers/2403.13157-matomaki-teravainen-notes.md`.

#### 2.4 Guth–Maynard — `arXiv:2405.20552`
**Title**: “New large value estimates for Dirichlet polynomials”

- **Target blocker**: RG **B2′** (same angle as above, but with stronger technology).
- **Deep-dive focus**:
  - Identify which Dirichlet polynomials they control (length, coefficients, norms).
  - Identify if results can be adapted to the Dirichlet polynomial approximants to \(\log \zeta\) or \(-\zeta'/\zeta\).
- **Success criterion**:
  - A pathway to bounding oscillation/variance of the renormalized tail on Whitney bases.

- **Deep-dive verdict**: best-in-class **toolkit** for modern zero density via Dirichlet polynomial large values, but still global/\(o(1)\)-level; not a direct Lean “constant-and-box” Carleson input.  
  See `notes/papers/2405.20552-guth-maynard-notes.md`.

#### 2.5 Pintz — `arXiv:2310.04544`
**Title**: “A remark on density theorems for Riemann’s zeta-function”

- **Target blocker**: RG **B2′** support paper (may sharpen or reframe density tools).
- **Deep-dive focus**:
  - Extract any improved constants or a sharpened form that localizes better.
- **Success criterion**:
  - Either: a usable improvement; or: document why it’s not helpful for μ-Carleson.

- **Deep-dive verdict**: mostly background/support, not directly actionable for current Lean holes.  
  See `notes/papers/2310.04544-pintz-notes.md`.

#### 2.6 Masatoshi Suzuki — `arXiv:2301.05779`
**Title**: “Li coefficients as norms of functions in a model space”

- **Target blocker**: Route 3 (conceptual match to `SesqMeasureIdentity` / Hilbert realization).
- **Deep-dive focus**:
  - Identify the Hilbert/model space used and the exact “norm = Li coefficient” statement.
  - Check whether the representation is “measure-first” (Clark measure / spectral measure) or an abstract Hilbert norm.
- **Mapping tasks**:
  - Translate the model space identity into something that resembles
    `SesqMeasureIdentity` or `ReflectionPositivityRealization` in `ExplicitFormula/MainRoute3.lean`.
  - Determine whether the paper provides any *bridge* from analytic properties of ξ/ζ to positivity of that model-space norm (even conditional statements help formal target-shaping).
- **Success criterion**:
  - A refined, more attackable intermediate target for Route 3 (even if still RH-equivalent).

- **Deep-dive verdict**: most relevant conceptual match to Route 3; suggests a more concrete intermediate “Hilbert model” target. Not a proof of the splice identity.  
  See `notes/papers/2301.05779-suzuki-notes.md`.

#### 2.7 Chourasiya — `arXiv:2412.02068`
**Title**: “An explicit version of Carlson’s theorem”

- **Target blocker**: Route 3 A2-style uniqueness / “contour vs boundary” identification steps (possible).
- **Deep-dive focus**:
  - Identify if the explicit Carlson statement can replace any analytic-continuation + growth arguments in the splice chain.
- **Success criterion**:
  - A concrete place in the Route‑3 identity chain where Carlson gives a shorter proof (or a more formalization-friendly proof).

- **Deep-dive verdict**: despite the title, the paper is about an explicit **Carlson-type zero density bound**; it supports only far-right zero control (B2′ support), not Route‑3 contour/boundary uniqueness.  
  See `notes/papers/2412.02068-chourasiya-notes.md`.

#### 2.8 Maynard–Pratt — `arXiv:2206.11729v2`
**Title**: “Half-isolated zeros and zero-density estimates”

- **Target blocker**: RG **B2′** (but via *local vertical structure*, not raw \(N(\sigma,T)\)).
- **Deep-dive focus**:
  - Extract the unconditional “half-isolated ⇒ short zero-detecting polynomial ⇒ rare” mechanism.
  - Check if their “cluster” formalism could plausibly be adapted to Whitney/Carleson boxes.
- **Deep-dive verdict**: strategically helpful for understanding what kind of *local structure control* might be needed, but not a direct route to Lean’s `MuCarleson` predicate.  
  See `notes/papers/2206.11729-maynard-pratt-notes.md`.

High-signal extracted shapes:
- **Half-isolated definition (local)**: within a ball of radius \((\log|\gamma_0|)^2\), nearby zeros are forced either (i) to sit vertically above with almost the same real part, or (ii) to lie noticeably to the left (see Definitions 8–9 in the notes).
- **Theorem 4 (unconditional)**: a half-isolated zero \(\rho_0\) in \([T,2T]\) yields a very short von-Mangoldt Dirichlet polynomial that is \(\ge (\log T)^{-C}\) at \(\rho_0\), for some \(Y\) in
  \[
    Y\in\Big[T(\log\log T)^3/\log T,\ \ T^{1/5}/\log\log T\Big].
  \]
  This implies half-isolated zeros are rare (Corollary 5: Density-Hypothesis-strength for that subfamily).

#### 2.9 Suzuki — `arXiv:2301.00421v3`
**Title**: “On the Hilbert space derived from the Weil distribution”

- **Target blocker**: Route 3 (Hilbert/model-space realization of Weil form; RH ⇔ Weil positivity).
- **Deep-dive focus**:
  - Extract the definition of the Weil distribution \(W\) and the RH ⇔ nonnegative-definite criterion.
  - Extract the RH-assuming identification of the completion \(H_W\) with a de Branges/model space (Theorem 1.1).
  - Decide if this gives a more concrete intermediate Lean target than the current `CayleyBridge` axiom packaging.
- **Deep-dive verdict**: extremely relevant for Route‑3 target shaping; still RH-equivalent (does not bypass the splice identity).  
  See `notes/papers/2301.00421-suzuki-weil-distribution-notes.md`.

#### 2.10 “Weil explicit sums and arithmetic spectral measures” — `arXiv:2311.08519v1`
**Title**: “A probabilistic interpretation of Weil’s explicit sums and arithmetic spectral measures”

- **Target blocker**: Route 3 (spectral-measure realization; reflection-positivity flavor).
- **Deep-dive focus**:
  - Extract the operator/spectral-theorem statements: truncated Weil sums as quadratic forms and as spectral integrals (Theorems 5/7/9).
  - Map to Lean’s `SesqMeasureIntegralIdentity` as an alternate route: “operator realization ⇒ measure identity”.
- **Deep-dive verdict**: very aligned with the desired *shape* (quadratic form ⇒ spectral integral), but translation into our current PSC/J(s) splice chain remains substantial.  
  See `notes/papers/2311.08519-weil-spectral-measures-notes.md`.

#### 2.11 Matsumoto–Suzuki — `arXiv:2409.00888v2`
**Title**: “\(M\)-functions and screw functions … zeros of the Riemann zeta function”

- **Target blocker**: Route 3 (alternate RH-equivalent **kernel positivity** formulation, compatible with reflection positivity).
- **Deep-dive focus**:
  - Extract the RH ⇔ screw-function criterion (Theorem 1.3) and see if it gives a better “typed bridge target” than PSC/J(s).
  - Extract the \(M\)-function/value-distribution formulas (Theorems 1.1/1.2) for context on what’s RH-equivalent vs what’s “extra” (LI assumptions).
- **Deep-dive verdict**: very relevant for *target shaping* (kernel positivity ⇔ RH), but not a direct discharge of current PSC splice axioms.  
  See `notes/papers/2409.00888-matsumoto-suzuki-notes.md`.

---

### 3) How we’ll decide “keep / drop” quickly

For each paper, after 60–90 minutes:
- **Keep** if we can write a candidate lemma statement that plugs into one of:
  - `OscillationTargetTail.lean` (μ-Carleson ⇒ tail BMO), or
  - `ExplicitFormula/ContourToBoundary.lean` (splice identity), or
  - `ExplicitFormula/HilbertRealization.lean` (`SesqMeasureIdentity`/`SesqMeasureIntegralIdentity`).
- **Drop** if the results are global/non-explicit in a way that cannot be localized to Carleson boxes, or if the “positivity” is already known RH-equivalent without giving a new angle on the bridge.

---

### 4) Suggested ordering (highest expected ROI first)

- **RG B2′ funnel**: Bellotti `2405.12545` → Tao–Trudgian–Yang `2501.16779` → Pintz `2310.04544`
- **Dirichlet polynomial / large values funnel**: Guth–Maynard `2405.20552` → Matomäki–Teräväinen `2403.13157`
- **Route 3 conceptual bridge**: Suzuki `2301.05779`
- **Aux uniqueness tool**: Chourasiya `2412.02068`

---

### 5) Next concrete step (if you want me to drive)

Next steps (now that the deep dives are written):

- **If prioritizing B2′**:
  - Thread a **near/far μ split** through the *Lean-facing assumptions* so we can treat the far regime as “external literature input” and isolate the hard near-\(1/2\) regime.
  - Consider an intermediate predicate inspired by Tao–Trudgian–Yang: a **windowed “energy/structure” bound for zeros** that is plausibly closer to Carleson packing than raw \(N(\sigma,T)\).

- **If prioritizing Route 3**:
  - Decide whether to introduce a Suzuki-style intermediate target in Lean on top of `ExplicitFormula/Li.lean`’s `LiFramework` (i.e. a typed “\(\lambda_n\) is an \(L^2\)-norm” package), and map it into the existing `CayleyBridge`/`SesqMeasureIdentity` pipeline.

- **If prioritizing Route 3′ (Connes / determinant approximants)**:
  - Use the new typed “Hurwitz / locally-uniform convergence gate”:
    - `RiemannRecognitionGeometry/ExplicitFormula/HurwitzGate.lean` (`HurwitzOffRealAxisInStripGate`)
    - `RiemannRecognitionGeometry/ExplicitFormula/ConnesHurwitzBridge.lean` (top-level RH target)
    - `RiemannRecognitionGeometry/ExplicitFormula/ConnesConvergenceBundle.lean` (spells out the remaining “missing steps” as named fields)
  - The only remaining hard step is then to prove locally-uniform convergence of the approximant entire functions
    (typically normalized regularized determinants / Fourier transforms) to `Ξ` **on closed substrips of** \(|\Im(t)|<1/2\).


