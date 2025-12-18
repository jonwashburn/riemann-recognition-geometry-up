# Written RH Paper Driver / Prompt (Recognition Geometry)

This file is meant to be **copy-pasted into chat** (or referenced) as the standing instructions for continuing the written proof work.

## Canonical target file

- **Primary paper (current working copy)**: `recognition-geometry-dec-18.tex`
- **Older archived snapshot**: `recognition-geometry-dec-14.tex` (do not edit unless explicitly requested)

## What you (the assistant) are doing

You are an autonomous editing/proof assistant. Your job is to iteratively turn `recognition-geometry-dec-18.tex` into a **journal-ready manuscript**:

- The paper should read as a complete proof **conditional on clearly stated assumptions**, and those assumptions should be steadily replaced by proofs (or weaker assumptions) as we succeed.
- Every step that is not yet unconditional must be **explicitly labeled** (Assumption/Lemma/Conjecture) and tracked in an **assumption ledger**.
- The paper must remain **internally consistent** (notation, references, theorem numbering) and should **compile** with `pdflatex`.

### Primary objective (non-negotiable)

**Finish an unconditional written proof of the Riemann Hypothesis in this manuscript.**

This means the real work is to **eliminate the Assumption Ledger** by turning each assumption into:
- a proved lemma (ideally standard, cited), or
- a strictly weaker assumption that we can then attack, or
- a clearly isolated “new math” claim with a concrete plan and interfaces that match the Lean code.

### Priority order (what to do first)

1. **Mathematical progress**: reduce or discharge items in the Assumption Ledger (A1/A2/…).
2. **Structure for progress**: refactor the paper so that each remaining wall is a small, named statement with precise hypotheses.
3. **Polish**: readability, exposition, formatting, tables, etc. (only after (1)–(2) for the current iteration).

## Operating procedure (every time you work)

1. **Read context**
   - Open `recognition-geometry-dec-18.tex` and identify the section(s) relevant to the new instruction.
   - Open this file (`WRITTEN_PROOF_PROMPT.md`) and apply its rules.

2. **Update this prompt file FIRST (yes, this file)**
   - Add the new instruction to **“Instruction Inbox”** with today’s date.
   - Translate it into 1–5 concrete edits under **“Next edits (short queue)”**.
   - If the instruction touches a “hard wall”, add/update an item under **“Hard walls backlog”** and link it to an assumption ID.

3. **Edit the paper**
   - Implement the requested changes in `recognition-geometry-dec-18.tex`.
   - Maintain journal style: definitions before use, explicit hypotheses, clear theorem chains, proper citations, no overclaims.

4. **Keep it compiling**
   - Run `pdflatex -interaction=nonstopmode -halt-on-error recognition-geometry-dec-18.tex` and fix any LaTeX errors you introduced.

5. **Post-edit cleanup**
   - Update the **Assumption Ledger** (below): mark items as `open / weakened / proved / removed`.
   - Update **Change Log** (below) with a 3–10 line summary of what changed.

## Quality bars (journal-ready)

- **No hidden axioms**: anything not proved in the paper is labeled and enumerated.
- **No ambiguous “we assume positivity”**: state the exact proposition (domain, measure class, regularity).
- **Stable notation**: one definition per symbol; maintain a notation index.
- **Citations**: every classical theorem used (Weil explicit formula, Li criterion, Herglotz/Carathéodory, GNS/RKHS) has a bib entry.
- **Conditional vs unconditional clarity**: theorems that depend on open assumptions must say so explicitly.

## Improvement loop (always-on, but low-churn)

After completing the user’s explicit request, do *one* improvement pass (only if it won’t cause large disruptive churn).
**But**: prefer an improvement that creates mathematical progress (e.g. replacing an assumption with a standard cited lemma) over purely stylistic edits.

- tighten theorem statements (remove vagueness like “sufficiently rich” by pointing to a definition or class),
- add missing citations,
- reduce repetition and convert narrative “strategy” into lemma-proof structure,
- align paper statements with the formal objects in `RiemannRecognitionGeometry/ExplicitFormula/` where possible.

If an improvement would require many edits, add it to “Hard walls backlog” instead of making a huge change.

## Versioning rule

When we hit any of these milestones, create a new dated snapshot `recognition-geometry-dec-XX.tex` and keep working in the newest file:

- we remove/replace a major assumption,
- we prove a previously assumed lemma,
- we restructure the main theorem chain,
- or the user explicitly requests a snapshot.

## Instruction Inbox (append-only)

- **2025-12-18**: Create this prompt/driver file and create a Dec-18 snapshot of the paper.
- **2025-12-18**: Start using this driver to push the written proof forward: add a paper-facing Assumption Ledger, decompose the Route~3 “spectral identity” into smaller named sub-claims (identity vs positivity vs analytic interchange/boundary limits), and add missing classical citations (Herglotz/Carathéodory, RKHS/GNS/OS as needed).
- **2025-12-18**: Tighten the Route~3 “spectral identity” assumptions so the \(H=L^2(\mu)\) step is formally correct (explicit \(L^2\) integrability, and if \(\mu\) is allowed to be complex/signed then use total variation \(|\mu|\)).
- **2025-12-18**: Split Assumption A2 into named sub-assumptions that mirror the actual analytic steps (Fourier inversion, Mellin inversion/change-of-variables, contour-to-boundary limits, Fubini/Tonelli interchanges) and reflect that split both in this driver and in the paper’s Assumption Ledger.
- **2025-12-18**: Start discharging A2 items: first, replace “Fourier inversion” (A2a) with a standard cited lemma for Schwartz functions, so A2a reduces to verifying Schwartzness/compatibility for the specific transforms \(F_f\).
- **2025-12-18**: Update the driver to make “unconditional RH proof” the explicit priority and to prefer mathematical progress (discharging assumptions) over polish whenever possible.
- **2025-12-18**: Align the driver’s assumption ledger with the repo’s *actual unconditional blockers* (see `REMAINING_WORK.md` / `PROOF_STATUS_CURRENT.md`): include the RG track gaps (Carleson-energy bottleneck + oscillation/BMO certificate + remaining classical-analysis axioms) alongside the Route~3 gaps.
- **2025-12-18**: Discharge B3 for the *written* proof by replacing “classical-analysis axioms” with precise standard citations and minimal hypothesis checks (still leaving Lean to later port/prove).
- **2025-12-18**: Chip away at A2d by splitting it into standard measure-theory interchanges (Fubini/Tonelli + dominated convergence) vs the genuinely RH-adjacent “prime-sum interchange” estimates; discharge the standard part in the written proof via citations and isolate the remaining analytic condition explicitly.
- **2025-12-18**: Discharge A2d3 for the written proof by routing prime-sum interchanges through the absolutely convergent region \(\Re(s)>1\) and then using analytic continuation/identity theorems to extend equalities, avoiding non-justified interchange at the critical line.
- **2025-12-18**: Discharge the *standard* part of A2c for the written proof by citing Hardy-space boundary limits (Fatou theorem) on a half-plane, and rewrite A2c so it reduces to verifying the needed Hardy/growth hypotheses for the specific functions appearing in Route~3.
- **2025-12-18**: Make the “extend equalities by analytic continuation” step fully explicit in the paper by adding a cited identity-theorem lemma and referencing it where we route prime-sum interchanges through \(\Re(s)>1\).
- **2025-12-18**: Make A2c2 explicit by naming the concrete Route~3 symbol \(J=\det_2/(O\,\xi)\) and stating the exact boundary/phase/log-derivative hypotheses required (Hardy/bounded-type + unimodular trace + phase regularity sufficient to interpret \(J'/J=\theta'\) a.e.).
- **2025-12-18**: Decompose the Route~3 “spectral identity” (A1) into splice-completion inputs matching `ExplicitFormula/ContourToBoundary.lean` (explicit-formula cancellation + phase–velocity identity + normalization + pair factorization), and mirror that decomposition in both the driver and the paper.
- **2025-12-18**: For the written proof, explicitly cite Lagarias’ survey (Thm 3.1 / Guinand–Weil explicit formula) as the source of the explicit-formula cancellation step in the splice-completion chain, so the remaining novelty is isolated to the phase–velocity/spectral-measure step.
- **2025-12-18**: Refactor the Route~3 theorem chain in the paper so the “assumption” matches the splice-completion interface (positive spectral measure + pair factorization + normalization), rather than a generic \(\exists\mu\) spectral identity.
- **2025-12-18**: Split A1 into A1a–A1d mirroring the splice chain (`explicit_formula_cancellation`, `phase_velocity_identity`, pair factorization, normalization) so each subclaim can be attacked independently in the written proof and in Lean.
- **2025-12-18**: Make A1b (phase–velocity identity) explicit in the paper/driver in the exact “test function” form used in Lean: \(\int \phi\,\theta' \,dt = -\pi\int \phi\, d\mu_{\mathrm{spec}}\), and record the a.e. density interpretation \(\theta'=-\pi\rho\) when \(\mu_{\mathrm{spec}}\ll dt\).

## Next edits (short queue)

- [x] Fix Assumption A1a/A1b in the paper so \(T:\mathcal{T}\to L^2(\mu)\) is well-defined (require \(F_f\in L^2(|\mu|)\) and positivity upgrades to \(\mu\ge0\)).
- [x] Add a dedicated “Assumption Ledger” section to the paper body (not just in repo docs).
- [x] Split “Route 3 reduction” into smaller named lemmas/assumptions that match Lean modules (spectral identity vs positivity of boundary measure vs interchange/Fubini/boundary limits).
- [x] Add citations for Herglotz/Carathéodory and (optionally) RKHS/GNS/OS.
- [x] Split A2 into A2a–A2d (paper + driver) and attach each to concrete Lean files/modules where the corresponding lemmas live.
- [x] Add a paper lemma “Fourier inversion for Schwartz functions” + citation, and update A2a to only require Schwartzness/compatibility of \(F_f\).
- [x] Reduce A2b (Mellin inversion/change-of-variables) to a proved log-Schwartz lemma derived from Fourier inversion; leave only the “verify log-Schwartz + match normalization” obligations.
- [x] Discharge B3 in the written proof: replace the “classical-analysis axioms” bullet with explicit theorem names + citations (JN, Fefferman–Stein duality, BMO→Carleson via Poisson extension, η–ζ relation/analytic continuation).
- [x] Add RG-track blockers (G1–G3) to the driver’s Assumption Ledger + Hard walls backlog, and mirror them in the paper’s Assumption Ledger section.
- [x] Split A2d into (i) standard interchanges (Fubini/Tonelli + dominated convergence) vs (ii) prime-sum interchange, and discharge (i) in the written proof via citations.
- [x] Discharge A2d3 for the written proof: add a cited lemma on absolute convergence of \(-\zeta'/\zeta\) Dirichlet series for \(\Re(s)>1\) and explain how analytic continuation avoids further prime-sum interchanges.
- [x] Discharge the standard part of A2c in the written proof: add a cited Hardy/Fatou boundary-limit lemma (half-plane) and reduce A2c to verifying \(H^p\)/growth hypotheses for the specific symbols.
- [x] Add a cited “identity theorem / analytic continuation” lemma to the paper and reference it in the A2d3 discussion.
- [x] Make A2c2 explicit (paper + driver): specify the symbol \(J\), the half-plane, which \(H^p\) (or bounded-type) hypothesis is needed, and the minimal phase regularity needed so \(J'/J=\theta'\) is meaningful a.e.
- [x] Decompose A1 (paper + driver) into the concrete splice-completion subclaims and point each subclaim at the corresponding Lean locus (`ContourToBoundary.lean`, `ZetaRightEdgePhaseLimit.lean`, `PSCSplice.lean`).
- [x] Add a precise Lagarias (2007) citation in the paper for the explicit-formula cancellation step (A1-cancel) and add the corresponding bibliography entry.
- [x] Refactor the Route~3 theorem chain assumptions to match splice completion (positive \(\mu_{\mathrm{spec}}\), factorization \(F_{\mathrm{pair}}=\overline{F_f}F_g\), normalization), and update the corresponding assumption labels/ledger text.
- [x] Split A1 into A1a–A1d (paper + driver), and update A1’s status/plan to track which pieces are “cite Lagarias” vs genuinely new.
- [ ] Make A1b (phase–velocity) explicit in both driver and paper, matching the Lean interface and clarifying the density interpretation.

## Assumption Ledger (paper-facing map)

Each assumption must have: **ID**, **statement (1–5 lines)**, **where used**, **status**, and a **next-proof plan**.

- **A1 (Route3 spectral identity via splice completion)**  
  - **Statement**: Identify the Weil pairing \(B(f,g)=W^{(1)}(f\star_m \widetilde{\overline g})\) with a positive-measure boundary pairing
    \[
      B(f,g)=\frac12\int_{\mathbb{R}} \overline{F_f(t)}\,F_g(t)\,d\mu_{\mathrm{spec}}(t),
    \]
    where \(F_f\) is the Route~3 boundary transform (Mellin/Fourier-normalized) and \(\mu_{\mathrm{spec}}\) is a positive spectral measure.  
  - **Where used**: `Route 3` theorem chain (spectral identity ⇒ RP realization ⇒ Weil gate ⇒ RH).  
  - **Status**: open  
  - **Next-proof plan**: prove the \emph{splice completion} chain matching `ExplicitFormula/ContourToBoundary.lean`:
    (i) an explicit-formula cancellation identity reducing \(W^{(1)}\) to a boundary pairing against the PSC boundary phase derivative,
    and (ii) a phase–velocity identity identifying that derivative with a positive boundary measure \(\mu_{\mathrm{spec}}\).
    The remaining analytic bookkeeping is normalization (the \(1/2\) factor) and the pair-factorization \(F_{\mathrm{pair}(f,g)}=\overline{F_f}\,F_g\).
  - **Lean locus**: `RiemannRecognitionGeometry/ExplicitFormula/ContourToBoundary.lean` (definitions `explicit_formula_cancellation`, `complex_phase_velocity_identity`, theorem `splice_completion_with_normalization`);
    `.../ZetaRightEdgePhaseLimit.lean` (right-edge limit scaffolding);
    `.../PSCSplice.lean` (wiring into the Route~3 pipeline).

- **A2 (Route3-FourierInversion / boundary limits)**  
  - **Statement**: the analytic inversion/limit/interchange steps needed to identify the transform side with the Weil functional, split as A2a–A2d below.  
  - **Where used**: construction of \(F_f\), justification of the identity in A1a.  
  - **Status**: open  
  - **Next-proof plan**: discharge A2a–A2d one-by-one, tightening hypotheses to the concrete test space used in Route~3.

- **A2a (Fourier inversion on test space)**  
  - **Statement**: Fourier inversion for the specific boundary transforms \(F_f\) used in Route~3.  
  - **Where used**: A1a identity (turn boundary integrals into \(F_f\)).  
  - **Lean locus**: `RiemannRecognitionGeometry/ExplicitFormula/ZetaFourierInversionWeil.lean`  

- **A2b (Mellin inversion / change-of-variables)**  
  - **Statement**: Mellin-side change-of-variables and inversion compatibilities aligning Lagarias normalization with multiplicative convolution/involution.  
  - **Where used**: A1a identity (normalization alignment).  
  - **Lean locus**: `.../MathlibBridge.lean`, `.../MulConvolution.lean`, `.../Lagarias.lean`  

- **A2c (Contour → boundary limits / right-edge limits)**  
  - **Statement**: boundary-limit results (Fatou-type / distributional boundary values) and right-edge limiting procedure needed to identify contour expressions with boundary objects. Split as A2c1–A2c2.  
  - **Where used**: A1a identity (contour-to-boundary reduction).  
  - **Status**: paper: A2c1 closed (cited), A2c2 open; Lean: open  
  - **Lean locus**: `.../ContourToBoundary.lean`, `.../ZetaRightEdgePhaseLimit.lean`, `.../LagariasContour.lean`  

- **A2c1 (Hardy/Fatou boundary limits on a half-plane)**  
  - **Statement**: if a holomorphic function lies in a Hardy space \(H^p\) on a half-plane, then it has a.e. nontangential boundary limits and Poisson representation.  
  - **Status**: paper: closed (standard); Lean: open  

- **A2c2 (Verify Hardy/growth hypotheses for the Route~3 symbols)**  
  - **Statement**: for the PSC ratio
    \(J(s)=\det_2(s)/(O(s)\,\xi(s))\) on \(\Omega=\{\Re(s)>1/2\}\),
    verify a bounded-type/Hardy hypothesis (e.g. \(J\in H^\infty(\Omega)\) or \(J\) is inner on \(\Omega\)) giving a.e. boundary limits,
    together with a measurable phase \(\theta\) such that \(J(1/2+it)=e^{i\theta(t)}\) a.e. and enough regularity on \(\theta\) (e.g. \(\theta\in W^{1,1}_{\mathrm{loc}}\))
    so that the boundary log-derivative identity \(J'/J=\theta'\) is meaningful a.e.  
  - **Status**: open  

- **A2d (Interchange: Fubini/Tonelli + prime-sum interchanges)**  
  - **Statement**: interchange steps needed to swap integrals, limits, and (where applicable) prime sums in the explicit formula manipulations. Split as A2d1–A2d3.  
  - **Where used**: A1a identity (justification of interchanges).  
  - **Status**: paper: A2d1/A2d2/A2d3 closed (cited/route through \(\Re(s)>1\)); Lean: open  
  - **Lean locus**: `.../Route3FubiniTonelliLemmas.lean` and dependent analytic files.

- **A2d1 (Fubini/Tonelli for the relevant integrals)**  
  - **Statement**: justify swapping iterated integrals by absolute integrability (or nonnegativity).  
  - **Status**: paper: closed (standard); Lean: open  

- **A2d2 (Dominated convergence / limit–integral interchange)**  
  - **Statement**: justify exchanging limits with integrals under an integrable dominating function.  
  - **Status**: paper: closed (standard); Lean: open  

- **A2d3 (Prime-sum interchange / absolute convergence control)**  
  - **Statement**: justify exchanging explicit-formula prime sums (or Dirichlet series expansions) with integrals/limits in the region of interest, using absolute convergence or uniform dominated bounds.  
  - **Status**: paper: closed (route through \(\Re(s)>1\) + analytic continuation); Lean: open  

### Route 3 (ExplicitFormula) assumptions (decomposed)

- **A1a (Explicit-formula cancellation / contour → boundary)**  
  - **Statement**: prove the explicit-formula cancellation step that reduces \(W^{(1)}(h)\) to a boundary integral against the PSC boundary phase derivative (Lagarias Thm 3.1 as the source statement; plus contour-to-boundary limit justifications).  
  - **Status**: open  
  - **Lean locus**: `.../ContourToBoundary.lean` (`explicit_formula_cancellation`, `..._contour`, and the right-edge limit scaffolding in `ZetaRightEdgePhaseLimit.lean`)

- **A1b (Phase–velocity / spectral measure identity)**  
  - **Statement**: identify the boundary phase derivative with a positive spectral measure \(\mu_{\mathrm{spec}}\) (the “phase–velocity identity”).
    In the current Lean interface (integrating \(\theta'(t)\) against Lebesgue measure), this is equivalent to requiring an a.e. density
    \[
      \theta'(t) = -\pi\,\rho(t)\quad \text{a.e.},\qquad \rho(t)\ge0,
    \]
    and then \(\mu_{\mathrm{spec}}=\rho(t)\,dt\).  
  - **Status**: open  
  - **Lean locus**: `.../ContourToBoundary.lean` (`PSCComponents.phase_velocity_identity`, `complex_phase_velocity_identity`)

- **A1c (Pair factorization of boundary transforms)**  
  - **Statement**: for \(h=\mathrm{pair}(f,g)\), the boundary transform factors as \(F_h=\overline{F_f}\,F_g\).  
  - **Status**: open  
  - **Lean locus**: `.../PSCSplice.lean` / test-space wiring

- **A1d (Normalization tracking)**  
  - **Statement**: track the global constants (the \(1/2\) factor) in the splice-completion identity.  
  - **Status**: mostly bookkeeping  
  - **Lean locus**: `.../ContourToBoundary.lean` (`splice_completion_with_normalization`) and the written lemma `splice completion (algebraic step)`

### Recognition Geometry (RG) track assumptions (Main.lean route)

- **B1 (RG bottleneck: Carleson energy budget)**  
  - **Statement**: discharge `RGAssumptions.j_carleson_energy_axiom_statement` (the “energy budget” per Whitney interval / tent region).  
  - **Where used**: RG main theorem (`RiemannRecognitionGeometry/Main.lean`) via the boundary-certificate / tail-budget chain.  
  - **Status**: open  
  - **Next-proof plan**: port the statement-shape from the HardyDirichlet blueprints (`REALITY_PORT_PLAN.md`) and prove it via a CR–Green + Carleson/Hardy pipeline (or VK-density packing bounds), explicitly tracking constants.

- **B2 (Oscillation certificate for \(\log|\xi|\))**  
  - **Statement**: produce `OscillationTarget := ∃ M, InBMOWithBound logAbsXi M ∧ M ≤ C_tail`.  
  - **Where used**: RG main theorem (`RiemannRecognitionGeometry/Main.lean`).  
  - **Status**: open  
  - **Next-proof plan**: prove a concrete BMO/oscillation bound for `logAbsXi` (or a replacement certificate) sufficient to feed the tail-budget inequality.

- **B3 (Remaining classical-analysis axioms in compiled RG modules)**  
  - **Statement**: replace remaining global `axiom` declarations (e.g. John–Nirenberg / Fefferman–Stein / BMO→Carleson embedding / η–ζ identity principle) by cited theorems or full proofs.  
  - **Where used**: RG track infrastructure and the “classical analysis inputs” bundle.  
  - **Status**: paper: closed (cited); Lean: open (axioms)  
  - **Next-proof plan**: for the written proof, cite standard references and state precisely how each theorem is used; for Lean, port/prove the needed forms gradually.

## Hard walls backlog (track + chip away)

These are “hard elements” that will take multiple iterations. Keep each item tight, with a target deliverable.

- **HW1: Route-3 spectral identity**  
  - **Deliverable**: a paper lemma “Spectral identity for \(W^{(1)}\)” with explicit hypotheses and a proof outline that cleanly separates: (i) explicit formula algebra, (ii) interchanges, (iii) boundary values.  
  - **Links**: Assumption A1.

- **HW2: Positivity of boundary measure / kernel**  
  - **Deliverable**: a precise statement equivalent to \(\mu\ge0\) (Pick/Schur kernel positivity, Herglotz representation) and a plan for proving it from the arithmetic input.  
  - **Links**: Assumption A1.

- **HW3: Fourier/Mellin inversion & change-of-variables**  
  - **Deliverable**: finalize the inversion lemmas needed to connect test-function transforms to the explicit formula (and remove the remaining Lean sorries in the Fourier inversion file).  
  - **Links**: Assumption A2.

- **HW4: RG Carleson-energy bottleneck (G1)**  
  - **Deliverable**: a paper lemma (with explicit constants and hypotheses) that implies `RGAssumptions.j_carleson_energy_axiom_statement`, plus a proof plan aligned with the HardyDirichlet blueprints.  
  - **Links**: Assumption B1.

- **HW5: RG oscillation certificate (G2)**  
  - **Deliverable**: a paper theorem producing an explicit oscillation/BMO certificate for \(\log|\xi|\) adequate for the RG chain, with a clear map to what must be formalized.  
  - **Links**: Assumption B2.

## Change Log

- **2025-12-18**: Created `WRITTEN_PROOF_PROMPT.md`. Created `recognition-geometry-dec-18.tex` as a snapshot and updated its `\\date{...}` to “December 18, 2025”.
- **2025-12-18**: Updated `recognition-geometry-dec-18.tex` with a paper-facing Assumption Ledger section; split Route~3’s “spectral identity” into separate (A1a) identity and (A1b) positivity assumptions; added standard references for \(H^p\)/Herglotz-Carathéodory, RKHS, and OS reflection positivity.
- **2025-12-18**: Tightened Route~3 Assumption A1a to a complex-measure form with \(F_f\in L^2(|\mu|)\) (total variation), so the \(H=L^2(\mu)\) realization step is formally correct once A1b (\(\mu\ge0\)) is assumed.
- **2025-12-18**: Split A2 into A2a–A2d (Fourier inversion; Mellin inversion/change-of-variables; contour-to-boundary/right-edge limits; Fubini/Tonelli + prime-sum interchanges) and mirrored that split in both the driver and the paper’s Assumption Ledger, with pointers to the corresponding Lean files.
- **2025-12-18**: Added a cited paper lemma for Fourier inversion on Schwartz functions and updated A2a so it reduces to verifying \(F_f\in\mathcal{S}(\mathbb{R})\) (with the chosen normalization).
- **2025-12-18**: Updated this driver to explicitly prioritize finishing an unconditional RH proof by discharging the Assumption Ledger (math progress first; polish last).
- **2025-12-18**: Added a paper lemma reducing Mellin inversion/change-of-variables (A2b) to Fourier inversion in a log-Schwartz setting; updated A2b so the remaining work is verifying log-Schwartz regularity and matching the Mellin normalization.
- **2025-12-18**: Discharged B3 for the written proof by replacing “classical-analysis axioms” with explicit standard citations (John--Nirenberg, Fefferman--Stein, BMO\(\to\)Carleson via Poisson extension, and \(\eta\)/\(\zeta\) analytic continuation references).
- **2025-12-18**: Discharged the standard part of A2d in the written proof by adding cited lemmas for Fubini/Tonelli (including series–integral interchange) and dominated convergence; isolated the remaining “prime-sum interchange” as the real analytic obligation (A2d3).
- **2025-12-18**: Discharged A2d3 for the written proof by citing absolute convergence of \(-\zeta'/\zeta\) on \(\Re(s)>1\) and routing prime-sum interchanges through that region, then extending equalities by analytic continuation.
- **2025-12-18**: Discharged the standard part of A2c for the written proof by adding a cited Hardy/Fatou boundary-limit lemma on a half-plane; reduced A2c to verifying the Hardy/growth hypotheses for the specific Route~3 symbols and matching boundary values.
- **2025-12-18**: Made the analytic-continuation step explicit by adding a cited identity-theorem lemma and referencing it in the A2d3 “route through \(\Re(s)>1\)” justification.
- **2025-12-18**: Made A2c2 explicit by naming the PSC ratio \(J=\det_2/(O\,\xi)\), stating the needed bounded-type/Hardy + unimodular phase-trace + phase-regularity hypotheses, and adding a lemma computing \(J'/J=\theta'\) under pointwise \(C^1\) trace regularity.
- **2025-12-18**: Decomposed A1 (Route~3 spectral identity) into splice-completion inputs (explicit-formula cancellation + phase–velocity identity + pair factorization + normalization) and pointed the written proof/driver to the corresponding Lean loci in `ExplicitFormula/ContourToBoundary.lean` and related files.
- **2025-12-18**: Added a small “splice completion algebra” lemma to the paper to make the cancellation + phase–velocity ⇒ measure-pairing step completely explicit (mirrors `splice_completion_with_normalization` in the Lean file).
- **2025-12-18**: Cited Lagarias’ survey (Thm.~3.1) as the source for the explicit-formula cancellation step in the Route~3 splice-completion chain; added a `Lagarias2007` bibliography entry.
- **2025-12-18**: Refactored the Route~3 theorem chain to assume the splice-completion spectral identity directly (positive \(\mu_{\mathrm{spec}}\) and the \(1/2\) normalization), aligning the paper’s assumption with the Lean splice pipeline.
- **2025-12-18**: Split Route~3 A1 into A1a–A1d (explicit-formula cancellation, phase–velocity identity, pair factorization, normalization) to match the splice-completion pipeline and make the remaining hard steps maximally explicit.
- **2025-12-18**: Made A1b (phase–velocity identity) explicit in the test-function form used in Lean, and recorded the a.e. density interpretation \(\theta'=-\pi\rho\) when \(\mu_{\mathrm{spec}}\ll dt\).


