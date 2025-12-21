### Deep-Dive Summary (shortlist)

This is a repo-facing summary that maps each deep-dived paper to the **exact blockers** in:
- written proof: `recognition-geometry-dec-18.tex`
- Lean: `RiemannRecognitionGeometry/` (notably `OscillationTargetTail.lean` and Route 3 files)

---

### 1) Route 3 (explicit formula / Weil–Li) relevance

- **Suzuki `arXiv:2301.05779`**
  - **Maps to**: Route 3 “Hilbert realization / reflection positivity” goal.
  - **Potential contribution**: RH-equivalent identity \(\lambda_n = c\|G_n\|^2_{L^2(\mathbb R)}\) with explicit \(G_n\), using model spaces \(K_\Theta\).
  - **Lean touchpoints**:
    - `RiemannRecognitionGeometry/ExplicitFormula/HilbertRealization.lean` (target shape)
    - `RiemannRecognitionGeometry/ExplicitFormula/CayleyBridge.lean` (bridge packaging)
  - **Verdict**: **Most relevant conceptually**; does not close the main RH-equivalent gap but suggests a more concrete intermediate target.
  - **Lean bridge target**: `RiemannRecognitionGeometry/ExplicitFormula/SuzukiBridge.lean`

- **Suzuki `arXiv:2301.00421v3`**
  - **Maps to**: Route 3 “Weil positivity ⇔ RH” and “Hilbert-space completion of the Weil form”.
  - **Key payload**: defines the Weil distribution \(W\) on \(C_c^\infty(\mathbb R)\), states RH ⇔ \(W\) is nonnegative definite, and (assuming RH) identifies the completion \(H_W\) with a de Branges/model space via Fourier inversion (Theorem 1.1).
  - **Lean touchpoints**:
    - `RiemannRecognitionGeometry/ExplicitFormula/HilbertRealization.lean` (the GNS/mechanical realization matches Suzuki’s “completion” story)
    - `RiemannRecognitionGeometry/ExplicitFormula/CayleyBridge.lean` (bridge packaging; still RH-equivalent)
  - **Notes**: `notes/papers/2301.00421-suzuki-weil-distribution-notes.md`

- **`arXiv:2311.08519v1`**
  - **Maps to**: Route 3 “spectral measure / operator realization” of the Weil explicit sum.
  - **Key payload**: constructs self-adjoint operators whose quadratic forms match truncated Weil sums, and expresses these quadratic forms as integrals against **spectral measures** (Theorem 7; Theorem 9 gives a \(q\to 1\) limit including the archimedean piece).
  - **Lean touchpoints**:
    - suggests an alternate intermediate target: “operator + spectral theorem ⇒ measure identity”, close to `SesqMeasureIntegralIdentity`.
    - `RiemannRecognitionGeometry/ExplicitFormula/OperatorSpectralMeasureBridge.lean` now makes this a **drop‑in Route‑3 target**: a `SpectralMeasureSesqIntegralIdentity` can be converted to a measure-first `SesqMeasureIntegralIdentity` (by absorbing `√w` into the transform), and then yields `OptionalTargets.ReflectionPositivityRealization` in one step.
  - **Notes**: `notes/papers/2311.08519-weil-spectral-measures-notes.md`

- **Matsumoto–Suzuki `arXiv:2409.00888v2`**
  - **Maps to**: Route 3 “kernel positivity / reflection positivity” formulations of RH.
  - **Key payload**: proves an RH-equivalent characterization via **screw functions**: a concrete \(g(t)\) built from a zero-sum satisfies “\(G_g\) is nonnegative definite” iff RH (Theorem 1.3), and also develops \(M\)-function/value-distribution identities under RH+LI.
  - **Lean touchpoints**:
    - suggests an alternate intermediate target: define `IsNonnegDefKernel` for a concrete kernel and show it implies RH.
  - **Notes**: `notes/papers/2409.00888-matsumoto-suzuki-notes.md`
  - **Lean bridge target**: `RiemannRecognitionGeometry/ExplicitFormula/ScrewFunctionBridge.lean`

- **Suzuki `arXiv:2206.03682v4`**
  - **Maps to**: Route 3 “kernel positivity / integral-operator” formulations of RH.
  - **Key payload**: RH ⇔ the specific zeta-attached function \(g(t)\) is a **screw function** (Theorem 1.2), plus RH ⇔ positivity/nondegeneracy of the associated integral-operator kernel on \([-a,a]\) (Theorems 1.3–1.4).
  - **Lean touchpoints**:
    - aligns almost verbatim with `ScrewFunctionBridge.lean`’s “screw criterion” target;
    - suggests optional stronger targets phrased via integral operators/eigenvalues (not yet encoded in Lean).
  - **Notes**: `notes/papers/2206.03682-screw-function-aspects-notes.md`

- **Connes–Consani–Moscovici `arXiv:2310.18423v2`**
  - **Maps to**: Route 3 “operator/quotient” realizations of zeta zeros and Weil positivity.
  - **Key payload**: packages the prolate operator via cyclic pairs and a grading operator, extends this to a semilocal setting, and gives a **zeros-as-spectrum** statement in a quotient framework (Proposition 3.6).
  - **Lean touchpoints**:
    - strongly motivates our operator→spectral-measure intermediate targets in `OperatorSpectralMeasureBridge.lean`;
    - matches the “quotient by radical / completion” mechanics already implemented in `HilbertRealization.lean`.
  - **Notes**: `notes/papers/2310.18423-prolate-wave-operators-notes.md`

- **Connes–Moscovici `arXiv:2112.05500v1`**
  - **Maps to**: the “prolate / Sonin / UV spectrum” backbone behind the Connes Route‑3′ program.
  - **Key payload**: constructs a self-adjoint prolate operator \(W_{\mathrm{sa}}\) with discrete spectrum on both sides and shows its **negative spectrum** has UV statistics matching squares of zeta zeros; constructs Dirac square roots whose imaginary-eigenvalue counting function matches the Riemann zero-counting asymptotic (Theorem 6.1).
  - **Verdict**: foundational support; not a direct discharge of PSC splice or RG B1/B2′ holes.
  - **Notes**: `notes/papers/2112.05500-prolate-spheroidal-operator-zeta-notes.md`

- **Connes `arXiv:2402.13082v1`**
  - **Maps to**: Route 3 operator/trace-formula motivation (heat kernels attached to “zero-spectrum operators”).
  - **Key payload**: assuming RH and assuming the existence of a self-adjoint operator whose spectrum is the imaginary parts of zeta zeros, computes the full small-\(t\) expansion of `Tr(exp(-t D^2))` using the Riemann–Weil explicit formula, and relates the divergent terms to the prolate-wave-operator Dirac square-root heat expansion.
  - **Lean touchpoints**:
    - supports the operator-first mindset behind `OperatorSpectralMeasureBridge.lean`, but does not itself supply a `SesqMeasureIntegralIdentity`.
  - **Verdict**: motivational/structural; not a blocker-discharge.
  - **Notes**: `notes/papers/2402.13082-heat-expansion-zeta-notes.md`

- **Connes–Consani–Moscovici `arXiv:2511.22755v1`**
  - **Maps to**: a new Route‑3′ operator/determinant approximation program (“finite primes → self-adjoint operators → zeros on the line”).
  - **Key payload**: constructs rank‑one perturbed scaling operators \(D_{\log}(\lambda,N)\) from **finite-prime** Euler products and a truncated Weil quadratic form; proves the associated regularized determinant is (up to an explicit factor) a Fourier transform \(\widehat{\xi}\) whose zeros are **all real** in the `Ξ(t)` spectral variable (hence on \(\Re(s)=1/2\) after the change of variables \(s=1/2+it\)). Numerical evidence suggests convergence of spectra to zeta zeros as \(N,\lambda\to\infty\).
  - **Lean touchpoints**:
    - aligns with the existing “operator / quotient-by-radical” mechanics (`HilbertRealization.lean`) and the operator-bridge targets (`OperatorSpectralMeasureBridge.lean`).
    - now also has an explicit typed “Hurwitz gate” for the final step:
      - `RiemannRecognitionGeometry/ExplicitFormula/HurwitzGate.lean`
      - `RiemannRecognitionGeometry/ExplicitFormula/ConnesHurwitzBridge.lean`
      - `RiemannRecognitionGeometry/ExplicitFormula/ConnesConvergenceBundle.lean` (typed surface for the Section 8 “missing steps”)
        - `ConnesMissingStepSimpleEven` (M1: ground state exists / even / simple, normalized by `ξ_λ(λ)=1`)
        - `ConnesMissingStep_kλ_approximates_ξλ` (M2: uniform-on-`[λ⁻¹,λ]` approximation `k_λ ≈ c_λ ξ_λ` with error → 0)
  - **Notes**: `notes/papers/2511.22755-zeta-spectral-triples-notes.md`

- **Connes–van Suijlekom `arXiv:2511.23257v1`**
  - **Maps to**: the foundational “self-adjoint quadratic form ⇒ real zeros” mechanism used by `arXiv:2511.22755`.
  - **Key payload**: proves (via generalized Carathéodory–Fejér + Hurwitz) that if a lower-bounded self-adjoint operator coming from a real-even distributional quadratic form has a simple isolated even ground state \(\xi\), then the Fourier transform \(\widehat{\xi}\) is entire with **only real zeros** (plus finite-dimensional Toeplitz / structured-matrix analogues).
  - **Lean touchpoints**:
    - suggests a reusable “real zeros from self-adjointness” intermediate target; complements our existing `Caratheodory.IsPositiveDefiniteKernelOn` route (Toeplitz/truncation-matrix positivity rather than analytic kernel positivity).
    - tiny glue lemma now lives in Lean: `RiemannRecognitionGeometry/ExplicitFormula/RealZeros.lean` (turns “all zeros real” into the `HurwitzGate` zero-free hypotheses).
  - **Notes**: `notes/papers/2511.23257-quadratic-forms-real-zeros-notes.md`

- **Connes–Consani `arXiv:2106.01715v1`** (published 2023)
  - **Maps to**: the foundational Connes/Consani “ζ-cycles” operator setup behind the later 2025 `Zeta Spectral Triples` program.
  - **Key payload**: defines the semilocal Weil quadratic form \(Q_{W,\lambda}\), explains its near-radical via the \(E\)-map and prolate spheroidal functions, and constructs perturbed spectral triples \(\Theta(\lambda,k)\) whose low eigenvalues numerically match low-lying zeta zeros; introduces ζ-cycles as the organizing concept.
  - **Lean touchpoints**:
    - supports the operator/quotient mechanics already present in `HilbertRealization.lean` and motivates the Route‑3′ “Hurwitz/convergence gate” approach.
  - **Notes**: `notes/papers/2106.01715-spectral-triples-zeta-cycles-notes.md`

- **`arXiv:2207.10419v1`**
  - **Maps to**: ζ-cycles as a Hochschild/trace-map/sheaf-theoretic package over the Scaling Site.
  - **Key payload**: identifies the trace map on Hochschild \(HH_0\) with the classical map \(E\) (as described in intro, Proposition 3.3) and states a sheaf/cohomological spectral realization of critical zeros (Theorems 1.1–1.2, intro).
  - **Verdict**: conceptual scaffolding; no immediate new discharge of current Lean proof holes.
  - **Notes**: `notes/papers/2207.10419-hochschild-trace-zeta-cycles-notes.md`

- **van Nuland–van Suijlekom `arXiv:2104.09899v2`**
  - **Maps to**: “echoes of the spectral action” background used in the structured-matrix story of `arXiv:2511.23257`.
  - **Key payload**: MOI-based Taylor expansions of the spectral action `Tr(f(D+V))`, producing explicit cyclic/Hochschild cocycles and convergence criteria for the expansion.
  - **Verdict**: background/support; does not address the Connes Route‑3′ missing step (determinant convergence to `Ξ`).
  - **Notes**: `notes/papers/2104.09899-cyclic-cocycles-spectral-action-notes.md`

- **Nagai `arXiv:2511.07495v1`**
  - **Maps to**: general Fredholm determinant / ζ-regularization folklore (sine-kernel / Painlevé‑V τ-function).
  - **Verdict**: drop/background only; no connection to zeta zeros / ξ/Ξ, and no discharge of Route‑3 or RG-track blockers.
  - **Notes**: `notes/papers/2511.07495-selector-kernels-fredholm-notes.md`

---

### 2) B2′ / μ-Carleson funnel relevance

The current Lean funnel is:

- `MuCarleson` (`RiemannRecognitionGeometry/MuCarleson.lean`)
  → `oscillationTargetTail_of_muCarleson` (axiom)
  → `OscillationTargetTail` (`RiemannRecognitionGeometry/OscillationTargetTail.lean`)

Recent papers mainly deliver **global** density/energy control, which can help in “far-right regimes” but not yet in the **near-critical-line, local Carleson-box** regime.

Lean-facing scaffolds added for this decomposition:
- `RiemannRecognitionGeometry/ZeroOrdinateEnergyAssumptions.lean` (energy/structure ⇒ near μ‑Carleson, stub)
- `RiemannRecognitionGeometry/ZeroDensityAssumptions.lean` (zero density ⇒ far μ‑Carleson, stub)

Intended literature inputs:
- **Near/energy scaffold**: Tao–Trudgian–Yang (additive energy of zeros), potentially via further localization lemmas.
- **Far/zero-density scaffold**: Bellotti / Chourasiya / Guth–Maynard-style density bounds (control only away from \(1/2\)).

- **Bellotti `arXiv:2405.12545`**
  - **Gives**: explicit log-free \(N(\sigma,T)\le C T^{B(1-\sigma)}\) for \(\sigma\) extremely close to 1 (plus a uniform specialization with \(B=1.448\)).
  - **Use**: controls zeros with \(\beta\) very close to 1 (i.e. large \(\beta-1/2\)).
  - **Verdict**: **Support only** (helps carve out an easy regime).

- **Chourasiya `arXiv:2412.02068`**
  - **Gives**: explicit Carlson-type \(N(\sigma,T)\le K(\sigma,T_0)T^{4\sigma(1-\sigma)}(\log T)^{5-2\sigma}\) for \(\sigma\ge 0.6\) (and an absolute-constant version highlighted in the abstract).
  - **Use**: controls zeros with \(\beta\ge 0.6\) (still “far” from 1/2).
  - **Verdict**: **Support only**.

- **Guth–Maynard `arXiv:2405.20552`**
  - **Gives**: modern large-values technology + improved (asymptotic) zero density exponents.
  - **Use**: likely part of any future serious number-theory input to B2′ (especially via “energy of large values” methods).
  - **Verdict**: **High-value toolkit**, but not directly a Lean plug-in without significant new local-geometry lemmas.

- **Tao–Trudgian–Yang `arXiv:2501.16779`**
  - **Gives**: systematic “best known” exponents for zero density and new **additive energy** bounds (Theorem 64).
  - **Use**: suggests an alternative intermediate target for B2′: prove a local energy/structure bound for zeros in Whitney windows, then derive μ-Carleson.
  - **Verdict**: **Strategic**; helps redesign the B2′ decomposition.

- **Matomäki–Teräväinen `arXiv:2403.13157`**
  - **Gives**: reduction “zero density ⇒ large-values bounds for Dirichlet polynomials”.
  - **Use**: supports a future chain “(some density input) ⇒ distribution control ⇒ BMO/oscillation control”.
  - **Verdict**: **Structural**; not directly discharging existing Lean axioms.

- **Pintz `arXiv:2310.04544`**
  - **Gives**: assorted density consequences, some conditional (e.g. Lindelöf ⇒ strong density in a right-hand range).
  - **Verdict**: **Background/support**.

- **Maynard–Pratt `arXiv:2206.11729v2`**
  - **Gives**: local/vertical structure technology (“half-isolated zeros”) + an unconditional implication “half-isolated ⇒ short detecting polynomials ⇒ rare”.
  - **Why it’s interesting**: it’s one of the few modern zero-density-adjacent papers that is explicitly *sensitive to vertical clustering*, which is closer in spirit to our Whitney/Carleson-box geometry than a raw global \(N(\sigma,T)\) exponent.
  - **Key definition shape**: a half-isolated zero is defined by a *local* exclusion condition in a ball of radius \((\log|\gamma_0|)^2\), forcing nearby zeros either to sit vertically above with nearly equal real part (\(|\beta'-\beta_0|\le 1/(10\log Y)\), \(\gamma'\ge\gamma_0\)) or to lie significantly to the left (\(\beta'\le \beta_0-(\log\log|\gamma_0|)^2/\log Y\)).
  - **What it doesn’t give**: no direct uniform local `MuCarleson` bound; their strongest near–Density-Hypothesis statement is conditional on a very rigid hypothesis (zeros on finitely many vertical lines).
  - **Notes**: `notes/papers/2206.11729-maynard-pratt-notes.md`

---

### 3) Immediate next steps (concrete)

- **If prioritizing B2′**:
  - Split μ into “near” and “far” regimes in the *written* argument, and cite Bellotti/Chourasiya/Guth–Maynard for the “far” regime.
  - Add a Lean-facing intermediate predicate capturing “energy/structure control in Whitney windows”, motivated by Tao–Trudgian–Yang, and aim to prove:
    - (energy/structure control) ⇒ `MuCarleson` ⇒ `OscillationTargetTail`.

- **If prioritizing Route 3**:
  - Decide whether to introduce a Suzuki-style intermediate target in Lean (model space / \(L^2\) norm identity for Li coefficients) as a more concrete instance of `SesqMeasureIdentity`.


