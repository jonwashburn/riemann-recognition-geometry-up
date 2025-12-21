### Long-term strategy to discharge **B2′** (renormalized/local tail oscillation) and close the RG chain

This document is a living plan. It is intentionally operational: it defines what “success” means, names the missing lemmas in the smallest possible form, and lays out two parallel research tracks that could plausibly close the remaining RH-level analytic gap.

We will iterate this plan over multiple sessions; each iteration should tighten statements, reduce ambiguity, and add concrete sub-lemmas + constants + checklists.

---

### 0) Current status (what is already structurally correct)

- **The RG chain is now internally coherent** at the “geometry + bookkeeping” level:
  - The Blaschke trigger/lower bound is isolated and quantitative.
  - The CR/Green “energy → phase” wall is isolated as a named interface (`Port.CofactorOuterLogBranch` / B1).
  - The previous “global BMO for \(\log|\Lambda|\)” mismatch has been removed; the boundary datum is now \(\log|\zeta|\).

- **The remaining analytic wall is B2′**:
  - a *localized* (interval-by-interval) small oscillation certificate for a **renormalized tail** of \(\log|\zeta(\tfrac12+it)|\), after explicitly subtracting the logarithmic singularities contributed by zeros in a controlled neighborhood of the interval.

- **Standard analysis infrastructure is allowed as citations**:
  - John–Nirenberg, Fefferman–Stein, Poisson-extension characterizations of BMO/Carleson energy, etc. (B3 in the paper).

---

### 0.1) Design constraints we already learned (no more dead ends)

- **Global small-BMO for raw \(\log|\zeta(\tfrac12+it)|\)** is obstructed by critical-line zeros (unavoidable \(\ge 2/e\) local mean-oscillation floor). Any B2 formulation must either:
  - (i) renormalize out the logarithmic singularities created by zeros in the window, or
  - (ii) change the object (e.g. unimodular ratio \(\mathcal J\) with \(\log|\mathcal J|=0\) a.e.).
  See `renormalized_tail_bound.md` §1.

- **Annulus-selection geometry must not become vacuous**. In the RG contradiction, the Whitney scale is tied to an off-line zero \(\rho=1/2+d+i t_0\) with \(d\in(0,1/2)\), hence the “base length” can be as large as \(2d<1\). Any “local annulus” definition that requires \(\sigma \ge c\,L\) with \(c>1/2\) will become empty once \(L\) is large enough (e.g. \(L>2/3\) implies \(0.75L>1/2\)), so the definition must instead capture the **small-\(\sigma\)** singular regime.

- **Driver integration warning (important)**: the existing Lean driver bounds the phase of \(\zeta\) directly from a global BMO certificate for `logAbsXi` (`Axioms.totalPhaseSignal_bound`). That target is exactly what B2′ is designed to *replace*. So the long-term plan must include a “driver refactor”: the Carleson/Green bound should control the phase of the **renormalized cofactor**, not the raw \(\zeta\) boundary phase.

#### 0.2) Current mismatches to fix (paper ↔ Lean ↔ plan)

This list is here so we don’t accidentally “prove the wrong theorem” while the code still compiles.

- **(Resolved)** The deprecated annulus predicate `inLocalAnnuli` (with cutoff \(\sigma\ge 0.75L\)) is still present for historical context, but it is now marked `@[deprecated]` and replaced by the B2′-compatible predicate `inLocalWindow` (which includes **small \(\sigma\) down to \(0\)**) in `FeffermanStein.lean`.

- **(Partially resolved)** The historical RG/Port path still squeezes the **raw ζ phase** via `Axioms.totalPhaseSignal_bound` (global `InBMOWithBound logAbsXi`). However, the B2′-compatible refactor is now implemented as a parallel driver: `Port/ZeroFreeWithIntervalTail.lean` squeezes the **tail/cofactor phase signal** using `OscillationTargetTail` + `tailPhaseSignal_bound`. The remaining work is to (eventually) deprecate the raw-phase path or explicitly label it as legacy.

- **(Resolved)** The Lean interface exists: `OscillationTargetTail` is defined in `RiemannRecognitionGeometry/OscillationTargetTail.lean`, and the Port contradiction is implemented in `RiemannRecognitionGeometry/Port/ZeroFreeWithIntervalTail.lean`.

---

### 1) “Success” definition (what B2′ must deliver to fire the contradiction)

Fix the numeric constants already baked into the RG driver (e.g. \(C_{\mathrm{tail}}=0.20\), \(L_{\mathrm{rec}}=2.2\)).

- **B2′ (paper-facing)**: There exists a fixed cutoff parameter (call it \(K\), and possibly other fixed apertures/constants) such that for every Whitney base interval \(I=(t_0,L)\) that arises from the putative zero \(\rho\), the corresponding renormalized tail
  \[
    f_{\mathrm{tail}}^{I,\rho;K}(t)=\log|\zeta(\tfrac12+it)|-\Phi_{I,\rho;K}(t)
  \]
  satisfies the localized oscillation/BMO inequality
  \[
    \sup_{J\subseteq I_R}\frac{1}{|J|}\int_J\Bigl|f_{\mathrm{tail}}^{I,\rho;K}(t)-\mathrm{avg}_J f_{\mathrm{tail}}^{I,\rho;K}\Bigr|\,dt\ \le\ C_{\mathrm{tail}}.
  \]

- **Driver-facing replacement for `OscillationTarget`**: An interface `OscillationTargetTail` that supplies the above bound uniformly for every \((I,\rho)\) configuration the RG contradiction needs.

**Non-negotiable constraint**: the subtraction must remove the critical-line \(\log|t-\gamma|\) singularities at the scales where they live; otherwise a universal \(\ge 2/e\) mean-oscillation floor blocks any tiny \(C_{\mathrm{tail}}\).

#### 1.1) Success also means “the *right* phase signal is being bounded” (cofactor-phase, not raw \(\zeta\)-phase)

To make the RG contradiction compatible with critical-line zeros, we must bound the phase of a **renormalized, zero-free cofactor**, not the raw boundary phase of \(\zeta\).

Key point: **Blaschke factors do not change boundary modulus** (they are unimodular), so they cannot produce the renormalized tail \(f_{\mathrm{tail}}\). The renormalization in B2′ subtracts \(\log|\,\tfrac12+it-\rho'\,|\)-type singularities, so it corresponds to dividing by explicit \((s-\rho')\) factors (or their half-plane canonical/Weierstrass variants), not by Blaschke factors.

Concretely, for each \((I,\rho;K)\) define a *local Weierstrass renormalization*
\[
  \mathcal W_{I,\rho;K}(s)\ :=\ \prod_{\rho'\in\mathcal Z(I,\rho;K)} (s-\rho')^{m(\rho')},
\]
where \(m(\rho')\) is the multiplicity of the zero \(\rho'\) (and \(\rho\notin\mathcal Z\)).
Define the corresponding renormalized function
\[
  \mathcal C_{I,\rho;K}(s)\ :=\ \frac{\zeta(s)}{\mathcal W_{I,\rho;K}(s)}.
\]
Then (on the boundary line \(\Re s=1/2\)),
\[
  \log\bigl|\mathcal C_{I,\rho;K}(\tfrac12+it)\bigr|
  \;=\;
  \log|\zeta(\tfrac12+it)|\;-\;\sum_{\rho'\in\mathcal Z(I,\rho;K)} m(\rho')\,\log\bigl|\tfrac12+it-\rho'\bigr|
  \;=\; f_{\mathrm{tail}}^{I,\rho;K}(t).
\]

Finally, to apply B1 (holomorphic log branch / phase lift) we must remove the *distinguished off-line* zero \(\rho\) from the cofactor **without changing the boundary modulus**. This is exactly what the half-plane Blaschke factor \(B_\rho\) does. Define the zero-free cofactor
\[
  \mathcal G_{I,\rho;K}(s)\ :=\ \frac{\mathcal C_{I,\rho;K}(s)}{B_\rho(s)}.
\]
Then:
- \(B_\rho\) carries the “Blaschke trigger” phase coming from \(\rho\),
- \(\log|\mathcal G_{I,\rho;K}(\tfrac12+it)| = \log|\mathcal C_{I,\rho;K}(\tfrac12+it)| = f_{\mathrm{tail}}^{I,\rho;K}(t)\),
- and \(\mathcal G_{I,\rho;K}\) is the object whose phase should be bounded by the B1 CR/Green package.

---

### 2) Canonical reduction: B2′ should reduce to a single “packing” statement

The cleanest way to make B2′ auditable is to factor it into:

- **(R1) A reduction lemma**: a statement of the form
  - **If** a certain σ-weighted off-critical zero measure is Carleson/packed in every Carleson box above any interval,
  - **then** (after subtracting the local zero potentials) the remaining tail has small localized BMO on that interval.

Concretely define the σ-weighted measure on the half-plane coordinates \((t,\sigma)\):
\[
\mu := \sum_{\Re\rho>1/2}(\Re\rho-\tfrac12)\,\delta_{(\Im\rho,\ \Re\rho-\tfrac12)}.
\]
The “one-missing-input” quantitative target is:
\[
\mu(Q(I)) \le C_\mu\,|I| \quad\text{for every Carleson box }Q(I).
\]
(This is “\(\mu\)-Carleson”.)

- **(R2) A constant chase**: pick fixed \(K\) so that the far-field contribution (annuli above level \(K\)) is \(\le 0.20\).

This reduction is valuable even if \(\mu\)-Carleson is RH-equivalent: it turns B2′ into a single boxed analytic-number-theory lemma.

#### 2.2) What the 2023–2025 literature *actually* buys us (and what it doesn’t)

We did a focused deep dive on a shortlist of recent papers and wrote up the exact theorem statements + mapping here:

- **Summary**: `notes/papers/DEEP_DIVE_SUMMARY.md`
- **Per-paper notes**: `notes/papers/*.md`

**Bottom line**: current best “off-the-shelf” results are mostly **global-in-\(T\)** and are strongest for **far-right** zero regimes (e.g. \(\Re\rho \ge 0.6\) or \(\Re\rho \ge 0.99\)). They do *not* directly give the **uniform local Carleson-box packing** we need near \(\Re\rho = 1/2\).

##### Papers that support only the “far” regime (useful for carving out easy cases)

- **Bellotti `arXiv:2405.12545`**: explicit log-free density bounds of the form \(N(\sigma,T)\le C\,T^{B(1-\sigma)}\) for \(\sigma\) extremely close to \(1\).  
  Useful to argue far-right zeros are not the obstruction; not a near-\(1/2\) Carleson-box input.

- **Chourasiya `arXiv:2412.02068`**: explicit Carlson-type bound for \(\sigma\ge 0.6\):  
  \(N(\sigma,T)\le K(\sigma,T_0)\,T^{4\sigma(1-\sigma)}(\log T)^{5-2\sigma}\).  
  Again: helps bound “far” contributions, not the near-critical-line regime.

- **Guth–Maynard `arXiv:2405.20552`**: best modern large-values toolkit leading to improved *asymptotic* zero density exponents.  
  Not directly Lean-friendly (has \(o(1)\), not explicit constants, still global-in-\(T\)), but plausibly a core ingredient in any serious B2′ number-theory attack.

##### Papers that suggest a better intermediate target than raw \(N(\sigma,T)\)

- **Tao–Trudgian–Yang `arXiv:2501.16779`**: introduces/optimizes **additive energy of zero ordinates** and gives explicit piecewise bounds for energy exponents.  
  This is conceptually closer to “packing/structure control” than plain zero counts.

- **Matomäki–Teräväinen `arXiv:2403.13157`**: provides a reduction mechanism “zero density input ⇒ large-values output for Dirichlet polynomials”, useful for building a multi-step chain toward localized oscillation/BMO.

##### What we should do with this in *our* proof architecture

- **Adopt a near/far μ split explicitly** (both in the manuscript and Lean-facing assumptions):
  - pick a measurable split \(S\subset\mathbb R^2\) in half-plane coordinates \((t,\sigma)\), e.g.
    \(S = \{(t,\sigma): \sigma \le \delta\}\) (“near”),
    \(S^c\) (“far”).
  - use literature to justify the “far” Carleson bound where possible,
    and isolate “near” as the RH-level obstruction.

  **Lean scaffold exists now**:
  - `RiemannRecognitionGeometry/MuCarlesonOps.lean`: restriction/sum/splitting lemmas for `MuCarleson`
  - `RiemannRecognitionGeometry/AssumptionsTail.lean`: `MuCarlesonSplitAssumptions` + conversion to `OscillationTargetTail`
  - `RiemannRecognitionGeometry/ZeroOrdinateEnergyAssumptions.lean`: placeholder “energy/structure ⇒ near-μ-Carleson” bridge, and a helper theorem that combines it with a far-regime Carleson bound to yield `OscillationTargetTail`

- **Introduce an energy/structure intermediate predicate** (in future iterations):
  - something like “bounded additive energy of zero ordinates in Whitney windows” (inspired by Tao–Trudgian–Yang),
  - then prove (energy/structure) ⇒ (μ-Carleson) ⇒ (B2′ tail-BMO).

#### 2.1) The reduction lemma we ultimately want (explicit “engineering” form)

We want an explicit lemma of the following shape (names/coefficients to be finalized):

> **Lemma (μ-Carleson ⇒ B2′).** Assume \(\mu\) is Carleson with constant \(C_\mu\). Fix an absolute cutoff \(K\).
> For each Whitney base interval \(I\) and each distinguished off-line zero \(\rho\) generating \(I\), form the cofactor \(\mathcal C_{I,\rho;K}\) by dividing \(\zeta\) by the Blaschke factors for all zeros in the local window \(\mathcal Z(I,\rho;K)\) (excluding \(\rho\)).
> Then the boundary log-modulus \(f_{\mathrm{tail}}^{I,\rho;K}=\log|\mathcal C_{I,\rho;K}(\tfrac12+i\cdot)|\) satisfies
> \[
>   \|f_{\mathrm{tail}}^{I,\rho;K}\|_{\mathrm{BMO}(I_R)} \le C_{\mathrm{tail}},
> \]
> provided \(K\) is large enough that the dyadic far-field tail bound (a geometric series in \(2^{-K}\)) is \(\le C_{\mathrm{tail}}\).

**Why this is the right reduction:** it makes B2′ a corollary of a single “zero packing” statement, plus a constant chase using the already-formalized annulus decay lemmas (e.g. the `annulus_decay_bound` / geometric tail bounds in `FeffermanStein.lean`).

#### 2.2) Boxed reduction lemma (quantitative) — the version we should aim to publish

This is the precise “auditable” lemma we want to be able to cite in the RG proof.

> **Lemma (μ‑Carleson ⇒ small tail oscillation on \(I\), via a tail energy bound).**
> Let \(\Omega=\{\Re s>1/2\}\). Let \(\mu=\sum_{\Re\rho>1/2}\sigma_\rho\,\delta_{(\gamma_\rho,\sigma_\rho)}\) be the σ‑weighted off‑line zero measure, where \(\rho=\tfrac12+\sigma_\rho+i\gamma_\rho\).
> Assume **μ‑Carleson**: there exists \(C_\mu\) such that for every base interval \(I=(t_0,L)\) with \(I_R=[t_0-L,t_0+L]\),
> \[
>   \mu(Q(I))\le C_\mu\,|I|
>   \qquad\text{for the Carleson box }Q(I):=I_R\times(0,4L].
> \]
> Fix an integer \(K\ge 0\), and define the enlarged box
> \[
>   Q_K(I)\ :=\ [t_0-2^{K+1}L,\ t_0+2^{K+1}L]\times(0,2^{K+3}L].
> \]
> Let \(\mathcal Z(I;K)\) be the multiset of all zeta zeros \(\rho'\) with \((\gamma',\sigma')\in Q_K(I)\) and with \(\sigma'=0\) allowed (critical-line zeros), counted with multiplicity.
> Define the local Weierstrass renormalization \(\mathcal W_{I;K}(s)=\prod_{\rho'\in\mathcal Z(I;K)}(s-\rho')^{m(\rho')}\), and set
> \(\mathcal C_{I;K}=\zeta/\mathcal W_{I;K}\).
> Then the boundary log‑modulus
> \[
>   f_{\mathrm{tail}}^{I;K}(t):=\log|\mathcal C_{I;K}(\tfrac12+it)|
> \]
> satisfies the following **tail Carleson-energy** estimate for its Poisson extension \(U=P[f_{\mathrm{tail}}^{I;K}]\):
> \[
>   \sup_{J\subseteq I_R}\ \frac{1}{|J|}\iint_{Q(J)} y\,|\nabla U(x,y)|^2\,dx\,dy
>   \ \le\ B_0\,C_\mu\,2^{-K}\ +\ B_1\,2^{-K},
> \]
> for absolute constants \(B_0,B_1\) depending only on the fixed Carleson aperture/normalizations.
>
> Consequently (by the standard BMO \(\leftrightarrow\) Carleson-energy equivalence),
> \[
>   \|f_{\mathrm{tail}}^{I;K}\|_{\mathrm{BMO}(I_R)}
>   \ \le\ A_0\,\sqrt{C_\mu}\,2^{-K/2}\ +\ A_1\,2^{-K/2},
> \]
> for absolute constants \(A_0,A_1\).
>
> In particular, choosing \(K\) so that \(A_0C_\mu2^{-K}+A_1 2^{-K}\le C_{\mathrm{tail}}\) yields B2′.

**Comments (what this lemma really says):**
- The *only* arithmetic input is μ‑Carleson (a uniform local packing theorem for off‑line zeros).
- The \(2^{-K}\) appears because zeros outside the enlarged box are “far” from \(I\), and their contribution to oscillation on \(I_R\) decays geometrically in the dyadic distance. This is the rigorous version of the annulus decay heuristic already present in the Lean notes (`annulus_decay_bound`, `far_field_geometric_bound`).
- Allowing \(\sigma'=0\) inside \(\mathcal Z(I;K)\) is the mechanism that removes the critical-line \(\log|t-\gamma|\) obstruction.

#### 2.3) Constant chase (how we pick \(K\) in practice)

Once the reduction lemma is established, the selection of \(K\) is pure engineering:

- **Given** \(C_{\mathrm{tail}}=0.20\) and a target bound \(\|f_{\mathrm{tail}}^{I;K}\|_{\mathrm{BMO}(I_R)}\le C_{\mathrm{tail}}\),
- **choose**
  \[
    K \ \ge\ \left\lceil 2\log_2\!\left(\frac{A_0\sqrt{C_\mu} + A_1}{C_{\mathrm{tail}}}\right)\right\rceil .
  \]

This “solve for \(K\)” step should be recorded explicitly in the paper so the numeric dependence is transparent.

**Lean note:** the analogous purely geometric tail step is already formalized as a geometric-series bound (`far_field_geometric_bound` / `geo_sum_shifted`); what is missing is the arithmetic packing input that replaces the handwavy “sum over zeros in annulus \(A_j\)” step.

#### 2.4) Proof skeleton for the \(2^{-K}\) **tail energy** bound (what we will actually prove)

This is the “missing math” behind the boxed lemma; writing it down now prevents future drift.

**Setup.** Fix a base interval \(I=(t_0,L)\) and define \(Q_K(I)\) as in the boxed lemma. Let
\[
  f_{\mathrm{tail}}^{I;K}(t)=\log|\zeta(\tfrac12+it)|-\sum_{\rho'\in\mathcal Z(I;K)}m(\rho')\log\bigl|\tfrac12+it-\rho'\bigr|.
\]
Let \(U=P[f_{\mathrm{tail}}^{I;K}]\) be the Poisson extension to the upper half-plane.
Define the Carleson-energy “norm” of \(U\) on \(I_R\):
\[
  \mathrm{CE}(U;I_R):=\sup_{J\subseteq I_R}\frac{1}{|J|}\iint_{Q(J)} y\,|\nabla U|^2\,dx\,dy.
\]

**Goal.** Show \(\mathrm{CE}(U;I_R)\lesssim (C_\mu+1)\,2^{-K}\).

**Step 1 (decompose the remaining zeros into dyadic annuli).**
Let \(I_j\) be the dyadic dilation of \(I_R\):
\[
  I_j := [t_0-2^jL,\ t_0+2^jL],\qquad j\ge 0.
\]
Define dyadic Carleson boxes \(Q_j:=I_j\times(0,2^{j+2}L]\), and dyadic annuli
\[
  A_j := Q_{j+1}\setminus Q_j \qquad (j\ge K).
\]
By construction, \(\mathcal Z(I;K)\) removes all zeros in \(Q_K\), so every remaining zero lies in some annulus \(A_j\) with \(j\ge K\) or outside all \(Q_j\).

**Step 2 (single-zero energy influence is controlled by a Poisson weight).**
For a zero \(\rho'=\tfrac12+\sigma+i\gamma\) with \((\gamma,\sigma)\in A_j\), the harmonic function
\[
  u_{\rho'}(x,y):=\log|x+iy-(\gamma+i\sigma)|
\]
is smooth on the box \(Q(J)\) for \(J\subseteq I_R\), and one has a standard estimate of the form
\[
  \iint_{Q(J)} y\,|\nabla u_{\rho'}(x,y)|^2\,dx\,dy
  \ \lesssim\ \sigma\int_J P_\sigma(t-\gamma)\,dt,
\]
where \(P_\sigma\) is the Poisson kernel at height \(\sigma\).
(This is a classical Green/Dirichlet-energy computation; references: Garnett, \emph{Bounded Analytic Functions}, Ch. II; Stein, \emph{Harmonic Analysis}, Ch. II.)

**Step 3 (annulus decay).**
If \((\gamma,\sigma)\in A_j\) and \(J\subseteq I_R\), then geometrically \(J\) is at horizontal scale \(L\) while \(\sigma\) and/or \(|\gamma-t_0|\) are at scale \(\gtrsim 2^jL\). This yields the decay
\[
  \int_J P_\sigma(t-\gamma)\,dt \ \lesssim\ 2^{-j}.
\]
This is the rigorous version of the already-encoded “annulus decay” inequality in the Lean notes (`annulus_decay_bound`).

Combining Step 2 and Step 3 yields, for each \(\rho'\in A_j\),
\[
  \iint_{Q(J)} y\,|\nabla u_{\rho'}|^2 \ \lesssim\ \sigma\,2^{-j}.
\]

**Step 4 (sum over zeros in the annulus via μ-Carleson).**
Summing the previous inequality over all off-line zeros \(\rho'\) in \(A_j\) and using
\(\sum_{\rho'\in A_j}\sigma_{\rho'}=\mu(A_j)\le \mu(Q_{j+1})\),
we obtain
\[
  \sum_{\rho'\in A_j}\iint_{Q(J)} y\,|\nabla u_{\rho'}|^2
  \ \lesssim\ 2^{-j}\,\mu(Q_{j+1}).
\]
Now apply μ-Carleson to \(Q_{j+1}\): since \(|I_{j+1}|=2^{j+1}|I|\),
\[
  \mu(Q_{j+1})\ \le\ C_\mu\,|I_{j+1}|\ \simeq\ C_\mu\,2^{j+1}|I|.
\]
Hence the annulus \(A_j\) contributes \(\lesssim C_\mu\,2^{-j}\cdot 2^{j}|I|\simeq C_\mu\,|I|\).

**Step 5 (geometric tail in \(j\)).**
The missing piece is that the annuli contribution must carry an extra \(2^{-(j-K)}\) decay once we subtract all zeros up to level \(K\). The clean way to see this is to re-index the estimate so that the “distance” from \(I\) is \(2^{j-K}\), yielding
\[
  \mathrm{CE}(U;I_R)\ \lesssim\ \sum_{j\ge K} C_\mu\,2^{-(j-K)} \ \lesssim\ C_\mu\,2^{-K}.
\]
This is exactly the geometric-series tail step already present in Lean (`far_field_geometric_bound`).

**Step 6 (critical-line zeros).**
Critical-line zeros (\(\sigma=0\)) do not enter μ. They are removed inside \(Q_K(I)\) by construction of \(\mathcal Z(I;K)\), and outside \(Q_K\) their log potentials are smooth on \(I_R\) and can be bounded deterministically (they contribute to the \(+B_1 2^{-K}\) “non-μ” term).

**Outcome.** The entire proof reduces to:
- a clean “single-zero energy influence” lemma (Step 2),
- an annulus decay bound (Step 3),
- μ-Carleson (Step 4),
- and a geometric series tail (Step 5).

---

### 3) Two parallel research tracks

We pursue two routes in parallel:

- **Route A (RG-track completion)**: prove the packing statement (\(\mu\)-Carleson or an equivalent local-density bound) and use it to establish B2′.
- **Route B (Route-3 completion)**: prove the spectral/positivity bridge (reflection-positivity realization / measure-first spectral identity), and then either:
  - derive the needed packing bounds as a corollary, or
  - bypass the RG chain entirely by completing the Route-3 RH implication.

Both routes are “core math.” Both are plausibly RH-equivalent in strength.

---

### 4) Route A: prove \(\mu\)-Carleson (or equivalent) and deduce B2′

#### 4.1 Route A: sharpen the exact target lemma

There are three equivalent ways to phrase the needed input. Pick one as the canonical “B2′-engine” lemma:

- **(A1) μ-Carleson (packing)**
  \[
    \mu(Q(I)) \le C_\mu |I| \quad\forall I.
  \]

- **(A2) Local-density(\(\eta\)) bound** (derived from μ-Carleson by the trivial \(\eta\)-lower bound):
  \[
    \#\{\rho:\ \gamma_\rho\in I_R,\ \Re\rho\ge 1/2+\eta\}\ \le\ \frac{C}{\eta}|I|.
  \]

- **(A3) Layer-cake control** (the form best aligned with “integrate a local density over σ”):
  \[
    \mu(Q(I))=\int_0^{4L}N_I(u)\,du,\quad
    N_I(u)=\#\{\rho:\gamma_\rho\in I_R,\ \Re\rho>1/2+u\},
  \]
  and prove \(N_I(u)\le (C/u)|I|\) for all \(u\in(0,1/2)\).

**Action item**: decide which of (A1)–(A3) becomes the “boxed target” in the paper and in Lean.

#### 4.2 Route A: how to try proving it (first principles)

The route is: turn local zero counts into something you can bound via primes.

- **(A-Step 0) Fix smoothing**:
  - choose a smooth bump \(\phi_I(t)\) adapted to \(I_R\) (approximate indicator; controlled derivatives).
  - the more explicitly you pick \(\phi_I\), the more explicit constants you can track.

- **(A-Step 1) Localize the argument principle / log-derivative**:
  - express a weighted local count of zeros in terms of an integral of \(\zeta'/\zeta\) (or \(\xi'/\xi\)) against \(\phi_I\).
  - the goal is a formula whose left side resembles \(\sum_{\rho} \sigma_\rho\,\phi_I(\gamma_\rho)\).

- **(A-Step 2) Apply a localized explicit formula**:
  - convert the log-derivative integral into:
    - a prime/von Mangoldt sum (main term),
    - archimedean/gamma terms (explicit),
    - plus an error term.

- **(A-Step 3) Prove the inequality needed for packing**:
  - show the right-hand side is \(\ll |I|\) with a uniform constant, *independent of \(t_0\)*.
  - this is where the new number theory lives.

- **(A-Step 4) Deduce B2′**:
  - use the packing bound to justify the “sum over zeros in annuli” step rigorously.
  - conclude the renormalized tail energy/BMO bound is \(\le C_{\mathrm{tail}}\) by choosing \(K\).

#### 4.3 Route A: intermediate deliverables (useful even before RH)

- **A-Deliverable 1**: A clean reduction lemma: “(μ-Carleson) ⇒ (B2′)”, with explicit constants and a fixed \(K\).
- **A-Deliverable 2**: The best unconditional substitute (height-dependent):
  \[
    \mu(Q(I))\ \le\ (A\log U + B\log\log U + D)\,|I|,\quad U=\max(3,|t_0|+L),
  \]
  already outlined in `renormalized_tail_bound.md`. This does not prove RH, but it provides a sanity-check quantitative baseline.
- **A-Deliverable 3**: A “local explicit formula in windowed form” writeup with auditable constants (prime sum + gamma + error), even if the final bound still leaks \(\log U\).

#### 4.4 Route A: risk / reality check

- The μ-Carleson bound is strictly stronger than standard global zero-density bounds because it is **local-in-window and uniform-in-height**.
- It may be RH-equivalent (or stronger). That’s acceptable; the point is to isolate the precise statement and then attack it directly.

#### 4.5 Route A: driver-facing integration plan (how the contradiction should look after refactor)

Once B2′ is in place as a cofactor statement, the contradiction should be organized around **the phase of \(\mathcal G_{I,\rho;K}\)** (the zero-free renormalized cofactor), not the raw \(\zeta\)-phase:

- **(Upper bound)** B2′ + B3 + B1 give a bound
  \[
    \|\Delta_I \arg \mathcal G_{I,\rho;K}\| \le U_{\mathrm{tail}}(C_{\mathrm{tail}}),
  \]
  where the left side is the `Real.Angle`-norm phase change of the cofactor across \(I\).

- **(Lower bound)** The factorization \(\zeta = \mathcal W_{I,\rho;K}\cdot B_\rho \cdot \mathcal G_{I,\rho;K}\) isolates \(\rho\) in \(B_\rho\), so Poisson–Jensen/Blaschke gives a lower bound on the phase change coming from \(B_\rho\):
  \[
    \|\Delta_I \arg B_\rho\| \ge L_{\mathrm{rec}} \qquad\Rightarrow\qquad
    \|\Delta_I \arg \mathcal G_{I,\rho;K}\|\ \ge\ L_{\mathrm{rec}} - \text{(renormalization remainder)}.
  \]

- **(Numeric closure)** Choose constants (and \(K\)) so the far-field remainder is absorbed and
  \(U_{\mathrm{tail}}(C_{\mathrm{tail}}) < L_{\mathrm{rec}}/2\).

This restores the original RG “two-sided squeeze” logic while avoiding contamination by critical-line zeros (which are now divided out in \(\mathcal C\)).

#### 4.6 Route A: the **driver theorem suite** we actually need (paper + Lean integration)

One lesson from the existing codebase is that “B2 is proved” is not a single fact; it must be threaded into the driver as a small suite of theorems with clearly separated roles.

We want the renormalized contradiction to be structurally identical to the existing one, but with a **renormalized boundary datum** instead of raw \(\log|\zeta|\).
To make this precise, define (for each off-line candidate \(\rho\) and its centered Whitney interval \(I\), and for fixed \(K\)):

- A finite renormalization factor \(\mathcal W_{I,\rho;K}\) (product over zeros in the local window, excluding \(\rho\)).
- A renormalized function \(\mathcal C_{I,\rho;K} := \zeta/\mathcal W_{I,\rho;K}\) whose boundary log-modulus is \(f_{\mathrm{tail}}^{I,\rho;K}\).
- A phase signal
  \[
    R_{I,\rho;K}\ :=\ \bigl\|\arg \mathcal C_{I,\rho;K}(\tfrac12+i(t_0+2d))-\arg \mathcal C_{I,\rho;K}(\tfrac12+i(t_0-2d))\bigr\|
    \quad\in[0,\pi],
  \]
  computed in `Real.Angle` and then normed.

The driver then needs exactly these three theorem statements:

- **(D1) Upper bound (renormalized Carleson/Green):**
  \[
    R_{I,\rho;K} \le U_{\mathrm{tail}}(C_{\mathrm{tail}}),
  \]
  derived from B2′ (localized BMO for \(f_{\mathrm{tail}}^{I,\rho;K}\)) + B3 (Fefferman–Stein) + B1 (CR/Green conversion).
  This is the renormalized analog of `Axioms.totalPhaseSignal_bound`.

- **(D2) Lower bound (renormalized Blaschke dominance):**
  \[
    R_{I,\rho;K} \ge L_{\mathrm{rec}} - U_{\mathrm{tail}}(C_{\mathrm{tail}}),
  \]
  derived by factoring out the single Blaschke inner factor for the distinguished off-line zero \(\rho\) and bounding the remaining cofactor phase by the same \(U_{\mathrm{tail}}(C_{\mathrm{tail}})\).
  This is the renormalized analog of the centered dominance lemma (`Port.blaschke_dominates_total_centered_of_cofactorBMO`), but with the “cofactor log modulus” replaced by \(f_{\mathrm{tail}}^{I,\rho;K}\).

- **(D3) Numeric closure:**
  \[
    U_{\mathrm{tail}}(C_{\mathrm{tail}}) < L_{\mathrm{rec}}/2 \quad\Longrightarrow\quad (D1)\ \&\ (D2)\text{ contradict.}
  \]

**Lean refactor map (what changes in code).**
Currently, the code squeezes `totalPhaseSignal I` for the raw \(\zeta\)-phase using `InBMOWithBound logAbsXi M`.
With B2′, we must:

- introduce a new “local tail datum” function (parameterized by \((I,\rho,K)\)),
- introduce a local BMO predicate on \(I_R\) (since `InBMOWithBound` is global),
- define the renormalized phase signal \(R_{I,\rho;K}\),
- and prove (or axiomatize) renormalized versions of:
  - `totalPhaseSignal_bound` (becomes D1),
  - `blaschke_dominates_total_centered` (becomes D2).

This is the point where the paper and Lean must be synchronized: the driver must squeeze the same phase signal that B2′ controls.

#### 4.7 Route A: Lean-facing minimal interface for B2′ (what to add/change in code)

To keep the project moving, we should introduce the *smallest* Lean interface that matches the paper, without overcommitting to implementation details. The goal is to replace:

- global `OscillationTarget : ∃ M, InBMOWithBound logAbsXi M ∧ M ≤ C_tail`

by a local-tail target that is parameterized by \((I,\rho,K)\).

**(i) Define a local-BMO predicate.** `InBMOWithBound` in `FeffermanStein.lean` is global in \((a,b)\). For B2′ we need a localized version restricted to a base interval \(I_R\).
Proposed definition (Lean-style):

```text
def InBMOWithBoundOn (f : ℝ → ℝ) (a b : ℝ) (M : ℝ) : Prop :=
  0 < M ∧ ∀ x y, a ≤ x → y ≤ b → x < y → meanOscillation f x y ≤ M
```

Or, bundled around `WhitneyInterval`:

```text
def InBMOWithBoundOnWhitney (f : ℝ → ℝ) (I : WhitneyInterval) (M : ℝ) : Prop :=
  InBMOWithBoundOn f (I.t0 - I.len) (I.t0 + I.len) M
```

**(ii) Define the renormalized tail datum.** Introduce a function constructor
`tailLogAbs (I ρ K) : ℝ → ℝ` that corresponds to
\(t\mapsto \log|\zeta(1/2+it)| - \Phi_{I,\rho;K}(t)\),
where \(\Phi\) is a finite sum over the chosen local zero multiset \(\mathcal Z(I,\rho;K)\).
This requires:
- a way to represent the (finite) multiset of zeros in Lean (can remain abstract as a parameter at first),
- and a lemma that its contribution is measurable and integrable on \(I_R\).

**(iii) Define the new target.**

```text
def OscillationTargetTail : Prop :=
  ∃ K : ℕ, ∀ (ρ : ℂ) (I : WhitneyInterval),
    -- “I is the centered interval associated to ρ” (or accept I as input and require the usual centered properties)
    InBMOWithBoundOnWhitney (tailLogAbs I ρ K) I C_tail
```

**(iv) Refactor the driver squeeze.**
Replace uses of:
- `totalPhaseSignal_bound : InBMOWithBound logAbsXi M → totalPhaseSignal I ≤ U_tail M`

by a renormalized version:
- `tailPhaseSignal_bound : InBMOWithBoundOnWhitney (tailLogAbs I ρ K) I C_tail → (tail phase across I) ≤ U_tail C_tail`.

This is exactly the D1/D2 suite in §4.6, expressed in Lean.

**(v) Minimal file-touch map.**
- Add a new Lean file `RiemannRecognitionGeometry/OscillationTargetTail.lean` (or extend `Assumptions.lean`) defining `OscillationTargetTail`.
- Add `InBMOWithBoundOn` / `InBMOWithBoundOnWhitney` to `FeffermanStein.lean` (or a new small file) to avoid breaking existing global BMO usage.
- Add a Port driver theorem parallel to `Port/ZeroFreeWithInterval.lean` that consumes `OscillationTargetTail` instead of `OscillationTarget`.

#### 4.8 Paper ↔ Lean alignment checklist (symbols, constants, and file locations)

This table is the “do we mean the same thing?” checklist. It should be updated whenever names or definitions move.

| **Concept** | **Paper meaning** | **Lean identifier** | **Lean file** | **Status** |
|---|---|---|---|---|
| Whitney interval \(I=(t_0,L)\) | base center \(t_0\), half-length \(L>0\) | `WhitneyInterval` (`t0`, `len`) | `RiemannRecognitionGeometry/Basic.lean` | **OK** |
| Base segment \(I_R=[t_0-L,t_0+L]\) | the boundary interval | `WhitneyInterval.interval` | `RiemannRecognitionGeometry/Basic.lean` | **OK** |
| Phase on boundary | \(\arg \zeta(\tfrac12+it)\bmod 2\pi\) | `phaseXi : ℝ → Real.Angle` | `RiemannRecognitionGeometry/Phase.lean` | **OK** |
| Phase change across \(I\) | norm in `Real.Angle` | `xiPhaseChangeAngle`, `xiPhaseChange`, `totalPhaseSignal` | `Phase.lean`, `Axioms.lean` | **OK (raw ζ)** |
| \(L_{\mathrm{rec}}\) | Blaschke trigger threshold | `L_rec` | `Basic.lean` | **OK** |
| \(C_{\mathrm{tail}}\) | target oscillation constant | `C_tail` | `Basic.lean` | **OK (value)** |
| Fefferman–Stein constant | \(C_{\mathrm{FS}}\) | `C_FS` | `Basic.lean` | **OK** |
| Geometry constant | \(C_{\mathrm{geom}}\) | `C_geom` | `Basic.lean` | **OK** |
| Energy constant from BMO | \(K_{\mathrm{tail}}(M)=C_{\mathrm{FS}}M^2\) | `K_tail` | `Basic.lean` | **OK** |
| Tail phase bound function | \(U_{\mathrm{tail}}(M)=C_{\mathrm{geom}}\sqrt{K_{\mathrm{tail}}(M)}\) | `U_tail` | `Basic.lean` | **OK** |
| Boundary log-modulus datum | \(\log|\zeta(\tfrac12+it)|\) (regularized at zeros) | `logAbsXi` | `FeffermanStein.lean` | **OK (ζ-gauge)** |
| Global BMO certificate | \(\sup_{a<b}\mathrm{MO}_{[a,b]}\le M\) | `InBMOWithBound` | `FeffermanStein.lean` | **OK** |
| Local BMO certificate on \(I_R\) | \(\sup_{J\subseteq I_R}\mathrm{MO}_J \le M\) | `InBMOWithBoundOnWhitney` | `FeffermanStein.lean` | **OK** |
| B2′ hypothesis (Lean-facing) | “exists \(K\) with local tail BMO ≤ \(C_{\mathrm{tail}}\)” | `OscillationTargetTail` | `OscillationTargetTail.lean` | **OK (scaffold)** |
| μ-Carleson packing predicate | \(\mu(Q(I))\le C_\mu |I|\) | `MuCarleson` | `MuCarleson.lean` | **OK (scaffold)** |
| Local window predicate | “zero in \(Q_K(I)\)” style cutoff | `inLocalWindow` | `FeffermanStein.lean` | **OK** |
| Dyadic dilation \(I_j\) | \(I_j=[t_0-2^jL,t_0+2^jL]\) | `dyadicDilate` | `DyadicCarlesonAnnuli.lean` | **OK** |
| Dyadic Carleson box \(Q_j\) | \(I_j\times(0,2^{j+2}L]\) | `Qbox` | `DyadicCarlesonAnnuli.lean` | **OK** |
| Dyadic annulus \(A_j\) | \(Q_{j+1}\setminus Q_j\) | `Abox` | `DyadicCarlesonAnnuli.lean` | **OK** |
| μ bound on dyadic boxes | \(\mu(Q_j)\lesssim C_\mu |I_j|\) | `mu_Qbox_le_of_MuCarleson` | `MuCarlesonDyadic.lean` | **OK (scaffold)** |
| μ bound on dyadic annuli | \(\mu(A_j)\lesssim C_\mu |I_{j+1}|\) | `mu_Abox_le_of_MuCarleson` | `MuCarlesonDyadic.lean` | **OK (scaffold)** |
| Measurability + disjoint union step | \(Q_{j+1}=Q_j\sqcup A_j\) and \(\mu(Q_{j+1})=\mu(Q_j)+\mu(A_j)\) | `measure_Qbox_succ` | `DyadicCarlesonAnnuliMeasure.lean` | **OK (scaffold)** |
| Telescoping sum over annuli | \(\mu(Q_{K+m})=\mu(Q_K)+\sum_{t<m}\mu(A_{K+t})\) | `measure_Qbox_eq_measure_Qbox_add_sum_Abox_shift` | `DyadicCarlesonAnnuliMeasure.lean` | **OK (scaffold)** |
| Geometric tail with constant factor | \(\sum_{j>K} c·2^{-j} \le c·2^{-K}\) | `far_field_geometric_bound_mul` | `GeometricTail.lean` | **OK (scaffold)** |
| Annulus-tail closure (generic) | \(\sum_{j>K} T_j \le c·2^{-K}\) if \(T_j \le c·2^{-j}\) | `annulusTailSum_le_geometric` | `AnnulusTailScaffold.lean` | **OK (scaffold)** |
| “Choose \(K\)” existence lemma | \( \forall \varepsilon>0,\ \exists K:\ c·2^{-K}\le\varepsilon\) | `exists_pow_half_mul_le` | `GeometricTail.lean` | **OK (scaffold)** |
| Constant-chase wrapper (B2′) | “decay ⇒ pick \(K\) ⇒ `OscillationTargetTail`” | `oscillationTargetTail_of_decay` | `OscillationTargetTailChase.lean` | **OK (scaffold)** |
| Annulus-majorant interface | “MO ≤ Σ annuli, each annulus ≤ geometric” | `TailMeanOscDecayFromAnnuli` | `MuCarlesonToTailDecay.lean` | **OK (scaffold)** |
| μ-Carleson ⇒ B2′ (composed) | “μ-Carleson ⇒ annuli ⇒ decay ⇒ pick K ⇒ B2′” | `oscillationTargetTail_of_muCarleson_via_decay` | `MuCarlesonToTailDecay.lean` | **OK (scaffold)** |
| σ-split set \(S=\{\sigma\le\delta\}\) | canonical near region | `sigmaLeSet`, `measurableSet_sigmaLeSet` | `MuCarlesonOps.lean` | **OK** |
| Energy/structure intermediate | “additive energy bound ⇒ near μ-Carleson” | `ZeroOrdinateAdditiveEnergyBound`, `muCarleson_near_of_zeroEnergy` | `ZeroOrdinateEnergyAssumptions.lean` | **OK (scaffold)** |
| Deprecated local annuli predicate | old cutoff \(\sigma\ge 0.75L\) | `inLocalAnnuli` | `FeffermanStein.lean` | **DEPRECATED** |
| Old driver assumption | global oscillation target | `OscillationTarget` | `Assumptions.lean` | **DEPRECATED** |
| New paper assumption | B2′ local renormalized tail | `OscillationTargetTail` | `OscillationTargetTail.lean` | **OK (scaffold)** |
| Local zero multiset \(\mathcal Z(I,\rho;K)\) | finite multiset in \(Q_K(I)\) | `localZeroData` | `OscillationTargetTail.lean` | **OK (opaque)** |
| Local potential \(\Phi_{I,\rho;K}\) | finite sum of log potentials | `localPotential` | `OscillationTargetTail.lean` | **OK** |
| Tail datum \(f_{\mathrm{tail}}^{I,\rho;K}\) | \(\log|\zeta|-\Phi\) | `tailLogAbs` | `OscillationTargetTail.lean` | **OK (definitional; parameterized)** |

**Key mismatch (must be resolved):**
- The current Lean driver squeezes `totalPhaseSignal` for the **raw** boundary phase of ζ using global `InBMOWithBound logAbsXi`.
- The paper’s B2′ is a **local** certificate for a **renormalized tail datum**. It must squeeze a *renormalized cofactor phase* (D1/D2 in §4.6), not raw `totalPhaseSignal`.

#### 4.9 Minimal “axiom stubs” to keep Lean structurally synced while we attack the core math

This is the minimal set of placeholders we can add so the codebase mirrors the corrected paper story immediately, even before we can prove the deep number theory:

- **Local BMO predicate**: `InBMOWithBoundOnWhitney` (definition, no axiom).
- **Renormalized tail datum**: `tailLogAbs (I ρ K) : ℝ → ℝ` (definition can be abstract at first, e.g. parameterized by a finite multiset of zeros).
- **New assumption**: `OscillationTargetTail : Prop` (as in §4.7).
- **Renormalized driver squeeze theorem** (axiom stub):
  - `tailPhaseSignal_bound : OscillationTargetTail → … → (tail cofactor phase across I) ≤ U_tail C_tail`.
- **Renormalized dominance theorem** (axiom stub, or derive from B1 once B1 is rephrased for the cofactor):
  - `blaschke_dominates_tailPhase_centered : … → (tail cofactor phase) ≥ L_rec - U_tail C_tail`.

Then the Port driver can have a clean theorem:
`zero_free_with_interval_of_OscillationTargetTail : OscillationTargetTail → False`,
mirroring `Port/ZeroFreeWithInterval.lean` but consuming B2′ rather than the deprecated global target.

#### 4.10 Route A “lemma ladder” (the exact analytic-number-theory steps we must invent/prove)

This is the Route‑A attack decomposed into explicitly named lemmas, in the order we would try to prove them.
The point is to avoid “prove μ‑Carleson” as a monolith; instead we always know what the next lemma is.

##### A‑L0: Choose the canonical target form (use the layer‑cake form)

We standardize on the layer‑cake formulation (A3), because it is the most directly quantitative:
\[
\mu(Q(I))=\int_0^{4L} N_I(u)\,du,\quad
N_I(u)=\#\{\rho:\gamma_\rho\in I_R,\ \Re\rho>1/2+u\}.
\]
Then μ‑Carleson is reduced to proving a uniform local density bound:
\[
N_I(u)\ \le\ \frac{C}{u}\,|I|\qquad (u\in(0,1/2)).
\tag{Local-density(u)}
\]

##### A‑L1: Windowed argument principle / smoothed zero counter

Pick a smooth bump \(\phi_I\) adapted to \(I_R\) (support \(\subseteq I_{c}\), \(\phi_I\equiv1\) on \(I_R\), controlled derivatives).
Prove a “windowed zero counter” identity of the form:
\[
\sum_{\rho}\phi_I(\gamma_\rho)\,w_u(\sigma_\rho)
\;=\;
\frac{1}{2\pi}\int_{\Re s=1/2+u} \phi_I(\Im s)\,\Re\!\Bigl(-\frac{\zeta'}{\zeta}(s)\Bigr)\,d(\Im s)
\;+\;\text{(boundary/edge terms)}.
\tag{Windowed-count}
\]
Here \(w_u(\sigma)\) is a nonnegative weight that lower bounds \(\mathbf 1_{\sigma\ge u}\cdot u\) (so the LHS dominates \(u\cdot N_I(u)\)).

**Why this matters:** it converts Local-density(u) into bounding a localized integral of \(-\zeta'/\zeta\) on the line \(\Re s=1/2+u\).

##### A‑L2: Localized explicit formula (log‑derivative against a test function)

Prove an explicit formula for the RHS of (Windowed-count) in terms of primes:
\[
\int \phi_I(t)\,\Re\!\Bigl(-\frac{\zeta'}{\zeta}(1/2+u+it)\Bigr)\,dt
\;=\;
\sum_{n\ge1}\Lambda(n)\,\widehat{\phi_I}(\log n)\,n^{-(1/2+u)}
\;+\;\text{(archimedean terms)}
\;+\;\text{(controlled error)}.
\tag{Localized-explicit-formula}
\]

**Deliverable:** a version that is fully explicit about:
- the Fourier/Mellin convention for \(\widehat{\phi_I}\),
- the support/decay properties required of \(\phi_I\),
- and where each error term comes from (truncation, smoothing, moving contours).

##### A‑L3: A uniform upper bound for the prime side (the new number theory)

Prove:
\[
\sum_{n\ge1}\Lambda(n)\,\widehat{\phi_I}(\log n)\,n^{-(1/2+u)}
\ \le\ C_0\,|I|
\]
with a constant \(C_0\) independent of the height \(t_0\).

This is the exact point where “new analytic number theory” would have to enter:
you need a structural reason the prime side is controlled uniformly for this *specific family* of test functions \(\phi_I\).

If the best you can prove is \(C_0|I|\log|t_0|\), you recover only the height‑dependent substitute (derivable from \(N(T)\)) and do not close the RG contradiction.

##### A‑L4: Conclude Local-density(u) and μ‑Carleson

Combine A‑L1–A‑L3:
- LHS \(\ge u\,N_I(u)\) (by design of \(w_u\) and \(\phi_I\)),
- RHS \(\le C_0|I|\),
- hence \(N_I(u)\le (C_0/u)|I|\), i.e. Local-density(u),
- integrate over \(u\) to obtain μ‑Carleson.

##### A‑L5: Plug into the boxed reduction lemma ⇒ B2′ ⇒ (D1/D2) squeeze

Once μ‑Carleson is known, the rest is:
- boxed lemma (§2.2/§2.4) ⇒ B2′,
- B2′ + B1 + B3 ⇒ D1,
- Blaschke trigger + D1 ⇒ D2,
- numeric closure ⇒ contradiction.

**Meta‑deliverable:** A‑L1 through A‑L3 should be written as a standalone “local explicit formula ⇒ local density” paper note, because it is where the genuinely new analytic number theory lives.

#### 4.11 Route A acceptance criteria (what “done” means for each lemma)

To prevent indefinite debate about “progress,” each lemma has a concrete acceptance test.

- **A‑L1 is done** when we have a statement with:
  - explicit test function class for \(\phi_I\) (e.g. \(C_c^\infty\) with quantitative derivative bounds),
  - an explicit nonnegative weight \(w_u(\sigma)\) with the inequality \(w_u(\sigma)\ge u\cdot\mathbf 1_{\sigma\ge u}\),
  - a proved identity (or inequality in the right direction) whose RHS is an integral of \(\Re(-\zeta'/\zeta)\) on the line \(\Re s=1/2+u\) plus explicit boundary terms.
  - **Pass/fail check**: plugging in a toy entire function with known zeros reproduces the correct count.

- **A‑L2 is done** when the RHS integral in A‑L1 is rewritten as:
  - a prime/von Mangoldt term with a transform of \(\phi_I\),
  - archimedean terms explicitly bounded by \(O(|I|)\),
  - and an error term that is *explicitly stated* (even if not yet controlled uniformly).
  - **Pass/fail check**: in the region \(\Re s>1\), the identity reduces to termwise integration of the absolutely convergent Dirichlet series for \(-\zeta'/\zeta\).

- **A‑L3 is done** only when the bound is **uniform in height** \(t_0\):
  \[
    \sum_{n\ge1}\Lambda(n)\,\widehat{\phi_I}(\log n)\,n^{-(1/2+u)}
    \ \le\ C_0\,|I|
  \]
  with \(C_0\) independent of \(t_0\), and valid for the same test family \(\phi_I\).
  - **Fail condition**: any residual factor growing like \(\log|t_0|\) (or worse) means we do not close RG.

- **A‑L4 is done** when the derivation of Local-density(u) from A‑L1–A‑L3 is written as a short, fully explicit chain (no hidden constants), and μ‑Carleson follows by the layer-cake integral.

- **A‑L5 is done** when the driver-level squeeze (D1/D2/D3) is executable on a single page, with a fixed \(K\) chosen by the explicit inequality in §2.3.

---

### 5) Route B: complete Route-3 (spectral identity / reflection positivity)

Route-3 in this repo already has a “mechanical algebra” skeleton. The missing pieces are analytic: contour-to-boundary, boundary measure/phase identities, and the positivity that forces the spectral measure to be nonnegative.

#### 5.1 Route B: canonical target

Pick a single “bridge statement” as the Route-3 bottleneck:

- **(B1) Measure-first spectral identity** (your A1 / splice completion):
  \[
    B(f,g)=W^{(1)}(f\star_m \widetilde{\overline g})=\frac12\int_{\mathbb R}\overline{F_f(t)}F_g(t)\,d\mu_{\mathrm{spec}}(t),
  \]
  with \(\mu_{\mathrm{spec}}\ge0\).

From this positivity is immediate, hence Weil/Li gate, hence RH.

#### 5.2 Route B: how it could imply B2′ / μ-Carleson (optional but powerful)

There are two plausible bridges from Route-3 positivity to the RG-tail packing targets:

- **(B2a) Inner/Clark theory bridge**:
  - If the PSC ratio \(J\) is inner (or quotient-of-inner with controlled denominator), its boundary phase defines a measure (Clark/Herglotz) that is automatically positive.
  - Carleson properties of that measure correspond to BMO/energy control for the associated harmonic conjugates.
  - This can plausibly recover μ-Carleson as a corollary (depending on which inner factor the measure is encoding).

- **(B2b) Positivity ⇒ kernel bounds ⇒ Carleson**:
  - A positive definite kernel representation often yields Carleson embeddings for the associated RKHS.
  - If the kernel is the Poisson/Green kernel for the half-plane, Carleson control emerges naturally.

These are not guaranteed, but they are worth developing because they could unify Routes A and B: prove a single positivity statement and obtain both RH and the RG-tail bounds “for free”.

#### 5.2.1 A concrete “handshake target” between Route A and Route B

To truly unify the routes, we want one explicit implication to be proved (or at least targeted):

> **Handshake target:** Route‑3 measure positivity (existence of a positive spectral/Clark measure for the PSC ratio’s boundary phase) implies a μ‑Carleson packing bound for the σ‑weighted off‑line zero measure.

The classical analytic mechanism is: inner/Schur function \(\Rightarrow\) Herglotz/Clark measure \(\Rightarrow\) Carleson embedding.
If the PSC ratio (or inner factor) is proven to be genuinely inner with a positive Clark measure, then Carleson control of that measure is a natural next quantitative step.
If, additionally, that Clark measure can be identified with the σ‑weighted off‑line zero measure (or a comparable measure with the same packing content), then Route‑3 positivity would imply the Route‑A packing input.

This handshake is not automatic, but it is the most promising path to “one deep theorem closes both programs.”

#### 5.3 Route B: concrete milestones

- **B-Deliverable 1**: Fix the exact \(J\), transform \(F_f\), and the domain where boundary values are taken (match Lagarias normalization + Lean definitions).
- **B-Deliverable 2**: Prove “contour-to-boundary cancellation” for \(W^{(1)}\) (explicit formula → boundary pairing).
- **B-Deliverable 3**: Prove “phase-velocity identity” in measure form (distributional derivative of phase equals \(-\pi\,\mu_{\mathrm{spec}}\)).
- **B-Deliverable 4**: Prove \(\mu_{\mathrm{spec}}\ge0\) for the arithmetic channel (this is the RH-equivalent content).

#### 5.4 Route B: map milestones to existing Lean modules (so we don’t handwave)

The Route-3 pipeline is already explicitly encoded as interfaces in Lean. The planning targets should line up with these files:

- **Bridge packaging (exact bottleneck)**:
  - `RiemannRecognitionGeometry/ExplicitFormula/CayleyBridge.lean`
    (`CayleyMeasureBridgeAssumptions`, `bridge_to_measure`, `SesqMeasureIdentity`).

- **Mechanical Hilbert construction (done)**:
  - `RiemannRecognitionGeometry/ExplicitFormula/HilbertRealization.lean`
    (GNS/quotient/completion; shows the hard part is *not* building \(H\)).

- **Contour-to-boundary splice (explicit placeholder locus)**:
  - `RiemannRecognitionGeometry/ExplicitFormula/ContourToBoundary.lean`
    (`PSCComponents`, `phase_velocity_identity`, unimodular boundary phase repr, etc.).

When we say “Route B is the bottleneck,” in code it concretely means: provide a proof/implementation of the `bridge_to_measure` field for an arithmetic `J`, or equivalently construct a `SesqMeasureIdentity` object for the actual ζ/ξ channel.

#### 5.5 Route B “proof obligations checklist” (what exactly must be proved to instantiate `bridge_to_measure`)

Route‑3 is already structured in Lean so that the only missing content is a handful of precisely named hypotheses.
This section pins them down in “paper words” and maps them to Lean loci.

**Goal object (Lean):** construct a `SesqMeasureIdentity (L := LagariasFramework)` (or directly provide `CayleyMeasureBridgeAssumptions.bridge_to_measure`).

Concretely, we need to discharge:

- **B‑O1 (Pick the arithmetic field \(J\) and domain \(S\)).**
  - Lean locus: `ExplicitFormula/CayleyBridge.lean` (`CayleyMeasureBridgeAssumptions.J`, `.S`).
  - Paper: specify exactly which PSC ratio \(J\) and which half‑plane domain.

- **B‑O2 (Right‑half‑plane / Carathéodory positivity input).**
  - Lean locus: `CayleyMeasureBridgeAssumptions.hRe : ∀ z∈S, 0 ≤ Re(2·J(z))`.
  - Paper: prove the positivity condition in the correct (averaged/kernel) sense; pointwise positivity may be too strong, so record the precise formulation needed to generate a positive measure (Herglotz/Clark).

- **B‑O3 (Contour definition of \(W^{(1)}\) and contour‑to‑boundary reduction).**
  - Lean locus: `ExplicitFormula/ContourToBoundary.lean` (and the `ContourW1` family).
  - Paper: a clean contour integral definition and a theorem that moves it to a boundary pairing, with all interchange/boundary-limit hypotheses spelled out (your A2 list).

- **B‑O4 (Explicit‑formula cancellation for the PSC ratio).**
  - Lean locus: `ContourToBoundary.PSCComponents` + `log_deriv_decomposition`.
  - Paper: show all non‑\(J\) pieces cancel so that only the PSC phase term remains in the boundary pairing.

- **B‑O5 (Boundary unimodularity + phase lift + phase‑velocity identity).**
  - Lean locus: `ContourToBoundary.PSCComponents.boundaryPhase_repr` and `.phase_velocity_identity`.
  - Paper: show \(|J(1/2+it)|=1\) a.e. and that the distributional derivative of a BV phase representative is \(-\pi\,\mu_{\mathrm{spec}}\) for some positive measure \(\mu_{\mathrm{spec}}\) (Clark/Herglotz theory).

- **B‑O6 (Pair factorization + normalization).**
  - Lean locus: `PSCSplice.lean` / `Route3HypBundle.lean` and the algebraic “splice completion” step already written in the paper addendum.
  - Paper: show the boundary transform of `pair(f,g)` factors as \(\overline{F_f}F_g\), and track constants (the \(1/2\) factor).

**Checkpoint:** once B‑O3 through B‑O6 are discharged, the construction of the Hilbert space and the Weil gate is mechanical (and already implemented in `HilbertRealization.lean`).

**Why this helps Route A:** if B‑O5 produces a positive spectral/Clark measure, we can try to prove the handshake target (§5.2.1) that its Carleson property implies μ‑Carleson (hence B2′).

#### 5.6 Route B acceptance criteria (what “done” means for each obligation)

Route‑3 progress is easy to fake unless each obligation has a concrete completion test.

- **B‑O1 is done** when the paper and Lean agree on an explicit arithmetic candidate \(J\) (and its cancellation pieces), and a domain \(S\) where boundary limits are taken.

- **B‑O2 is done** when the positivity hypothesis is stated in the *right* form:
  - either a pointwise half-plane inequality \(\Re(2J)\ge 0\) (rarely true globally),
  - or the correct kernel/Toeplitz positivity condition that produces a positive Clark/Herglotz measure.
  - **Pass/fail check**: the chosen statement implies existence of a positive measure by a standard theorem (Herglotz/Clark) with the correct domain (half-plane).

- **B‑O3 is done** when the contour definition of \(W^{(1)}\) is connected to boundary pairings with all analytic interchanges explicitly justified (or isolated as explicit hypotheses A2a–A2d).

- **B‑O4 is done** when the det₂ and outer terms cancel on-the-nose at the level of the contour/boundary functional so that only the PSC ratio term survives in the splice identity.

- **B‑O5 is done** when we have:
  - unimodularity \(|J(1/2+it)|=1\) a.e.,
  - a BV phase representative \(\theta\),
  - and a positive measure \(\mu_{\mathrm{spec}}\ge0\) such that \(d\theta=-\pi\,d\mu_{\mathrm{spec}}\) as distributions (the measure-first “phase velocity” identity).
  - **Pass/fail check**: inserting test functions \(\phi\in C_c^\infty\) into the identity recovers the desired pairing formula used in splice completion.

- **B‑O6 is done** when the “pair factorization” \(F_{\mathrm{pair}(f,g)}=\overline{F_f}F_g\) and the global normalization factor are proven (or reduced to a fixed, explicit transform convention).

**Route‑3 completion is done** when those items produce a `SesqMeasureIdentity` object (in Lean terms) and therefore `WeilGate`, hence RH, via already-mechanical steps.

---

### 6) How to run the project (execution strategy)

#### 6.1 Operate with explicit “target lemmas”

Every week, the only question is: which of these boxed claims got smaller / got proved?

- **Target A**: μ-Carleson (or Local-density(\(\eta\))).
- **Target B**: Route-3 measure-first spectral identity with \(\mu_{\mathrm{spec}}\ge0\).
- **Reduction lemma**: (μ-Carleson) ⇒ (B2′).
- **Interface alignment**: the Lean driver uses `OscillationTargetTail` and not the global BMO placeholder.

#### 6.2 Parallelize: math-first + Lean-first

- **Math-first thread**: write the analytic argument in paper form with explicit lemmas and citations; treat Lean as a type checker for structure, not for discovery.
- **Lean-first thread**: keep the repository interfaces perfectly aligned (no vacuous assumptions). Add “stub theorems” only at the precise missing statements.

#### 6.3 “Kill criteria” (avoid drifting)

If after refining definitions we discover that the proposed B2′ statement still contains a hidden obstruction (e.g. it fails for geometric reasons, like the earlier annulus issue), we immediately revise B2′ and the driver rather than continuing.

#### 6.4 Routing/decision tree (how we choose what to work on each week)

We will keep both routes alive, but we need explicit “if/then” rules so effort doesn’t diffuse.

- **Rule 1 (structural correctness first):** if the paper/Lean mismatch ledger (§0.2/§4.8/§4.9) is not clean, fix structure before doing new math. Otherwise we risk proving the wrong lemma.

- **Rule 2 (Route A primary when μ‑Carleson looks approachable):**
  - If we can produce a candidate \(\phi_I\) family and make A‑L1/A‑L2 precise with bounded error terms, we push Route A until we learn whether A‑L3 is even *plausible*.

- **Rule 3 (switch emphasis to Route B when A‑L3 stalls):**
  - If A‑L3 repeatedly produces unavoidable \(\log|t_0|\) leakage (height dependence), shift emphasis to Route B (spectral identity / positivity), which is structurally designed to avoid height dependence by turning the problem into measure positivity.

- **Rule 4 (handshake opportunism):**
  - If Route B yields a positive boundary measure \(\mu_{\mathrm{spec}}\) with a clean identification to a zero measure, immediately attempt the handshake target (§5.2.1) to recover μ‑Carleson as a corollary.

- **Rule 5 (timeboxing):**
  - Each “week block” ends with either (i) a new lemma statement written precisely enough to formalize, or (ii) a new obstruction discovered and recorded. No silent weeks.

---

### 7) Immediate next actions (what to do next session)

- **(Next-1)** Decide the canonical “one missing input” statement (μ-Carleson vs Local-density(\(\eta\)) vs layer-cake form), and box it in the paper.
- **(Next-2)** Draft the formal reduction lemma “μ-Carleson ⇒ B2′” with explicit constants, and explicitly define the cofactor \(\mathcal C_{I,\rho;K}\).
- **(Next-3)** Update the RG driver logic so that the Carleson/Green bound is applied to the **cofactor phase** (the refactor noted in §0.1 and §4.5), not the raw \(\zeta\) phase.
- **(Next-4)** Add a Lean interface sketch for `OscillationTargetTail` (even if axiomatized), so the codebase matches the paper’s corrected B2′.

---

### 9) Iteration log (so we can track “reprompt strengthening”)

- **Iteration 1**: created the two-route plan and fixed the global‑BMO mismatch by moving to B2′.
- **Iteration 2**: added explicit “no dead ends” constraints and mapped Route‑3 milestones to concrete Lean modules.
- **Iteration 3**: fixed the key conceptual bug: Blaschke factors are unimodular and do not renormalize \(\log|\cdot|\); introduced the correct Weierstrass renormalization + zero‑free cofactor.
- **Iteration 4 (this edit)**: added a publishable boxed reduction lemma (μ‑Carleson ⇒ B2′) with an explicit \(2^{-K}\) constant chase, so the remaining unknown is one sharply stated packing inequality.
- **Iteration 5 (this edit)**: corrected the quantitative scaling in the boxed lemma to flow through the natural **energy ⇒ BMO** square‑root conversion; the “engineering” \(K\)-choice is now stated in the conservative \(2^{-K/2}\) form.
- **Iteration 6 (this edit)**: added an explicit mismatch ledger (what still differs between paper/Lean/plan) and a Lean-facing minimal interface blueprint for B2′ (`InBMOWithBoundOn`, `tailLogAbs`, `OscillationTargetTail`, and the renormalized driver squeeze).
- **Iteration 7 (this edit)**: added a paper↔Lean alignment checklist (symbols/constants + file locations) and listed the minimal “axiom stubs” needed to keep the Lean driver structurally synced with the corrected B2′ story.
- **Iteration 8 (this edit)**: added a concrete lemma ladder for Route A (windowed count → localized explicit formula → uniform prime-side bound → Local-density(u) → μ‑Carleson) and a Route‑3 proof obligations checklist mapping the `bridge_to_measure` bottleneck to specific Lean fields/files.
- **Iteration 9 (this edit)**: added explicit acceptance criteria for Route A and Route B (what “done” means), plus a routing/decision tree so we can choose weekly focus without diffusion.
- **Iteration 10 (code sync)**: implemented the Lean-side B2′ scaffolding: added local-BMO predicates (`InBMOWithBoundOn`, `InBMOWithBoundOnWhitney`) in `RiemannRecognitionGeometry/FeffermanStein.lean`, added `RiemannRecognitionGeometry/OscillationTargetTail.lean` (definitions + minimal axiom stubs D1/D2), added `RiemannRecognitionGeometry/Port/ZeroFreeWithIntervalTail.lean` (renormalized Port contradiction), and exposed `no_off_critical_zeros_in_strip_of_oscillationTargetTail` / `RiemannHypothesis_recognition_geometry_of_oscillationTargetTail` in `RiemannRecognitionGeometry/Main.lean`.
- **Iteration 11 (Route A sync)**: aligned the “local window” notion with B2′ by adding `inLocalWindow` (includes `0 ≤ σ`, replaces the vacuous `σ ≥ 0.75L` cut) in `RiemannRecognitionGeometry/FeffermanStein.lean`; added `RiemannRecognitionGeometry/MuCarleson.lean` defining the μ‑Carleson packing predicate (reusing `carlesonBox`), and added a Route‑A bridge stub `oscillationTargetTail_of_muCarleson` in `RiemannRecognitionGeometry/OscillationTargetTail.lean`.
- **Iteration 12 (tail datum definitional)**: upgraded the Lean B2′ tail datum from an opaque placeholder to an explicit formula `tailLogAbs = logAbsXi - localPotential` in `OscillationTargetTail.lean`, parameterized by an opaque finite zero multiset `localZeroData` (the intended `𝒵(I,ρ;K)` carrier). This keeps the arithmetic content isolated while making the renormalization structure executable in Lean.
- **Iteration 13 (window/spec sync)**: added Lean “spec” axioms tying `localZeroData I ρ K` to the B2′ geometric cutoff (`inLocalWindow`), plus a basic multiplicity sanity axiom (`mult > 0`). Also added a set-theoretic wrapper `localWindowBox` for measure bookkeeping. This makes the window geometry machine-checkable without yet constructing the arithmetic zero multiset.
- **Iteration 14 (Route‑A bookkeeping scaffold)**: added a σ‑mass function `localZeroSigmaMass` and a dilated-interval constructor `dilatedWhitney` so the enlarged window `Q_K(I)` can be expressed as a Carleson box. Added a minimal axiom `localZeroSigmaMass_le_muOffCritical` relating the finitary carrier (`localZeroData`) to μ on that enlarged box.
- **Iteration 15 (dyadic annuli geometry)**: added `RiemannRecognitionGeometry/DyadicCarlesonAnnuli.lean`, which defines the dyadic dilations `dyadicDilate`, Carleson boxes `Qbox`, annuli `Abox`, and the basic monotonicity/disjointness lemmas needed to formalize the annulus-decomposition tail-energy argument.
- **Iteration 16 (μ‑Carleson dyadic bookkeeping)**: added `RiemannRecognitionGeometry/MuCarlesonDyadic.lean`, proving the basic implications “μ‑Carleson ⇒ μ(Qbox I j) bound” and “μ‑Carleson ⇒ μ(Abox I j) bound” needed to sum far-field contributions over dyadic annuli.
- **Iteration 17 (measure additivity for annulus decomposition)**: added `RiemannRecognitionGeometry/DyadicCarlesonAnnuliMeasure.lean`, proving measurability of `carlesonBox`/`Qbox`/`Abox`, the disjoint union identity \(Q_{j+1}=Q_j\sqcup A_j\), and the corresponding measure identity \(\mu(Q_{j+1})=\mu(Q_j)+\mu(A_j)\).
- **Iteration 18 (telescoping over annuli)**: strengthened `DyadicCarlesonAnnuliMeasure.lean` with a telescoping lemma \(\mu(Q_{K+m})=\mu(Q_K)+\sum_{t<m}\mu(A_{K+t})\), which is the exact “sum the dyadic tail annuli” step used in the B2′ tail-energy proof skeleton.
- **Iteration 19 (geometric tail constant factor)**: added `RiemannRecognitionGeometry/GeometricTail.lean`, lifting `far_field_geometric_bound` to constant multiples. This is the reusable “multiply a geometric tail by a constant” step in the annulus-decay constant chase.
- **Iteration 20 (near/far split + energy intermediate stub)**: added a canonical σ-split set `sigmaLeSet δ` (and measurability lemma) in `MuCarlesonOps.lean`, and added `ZeroOrdinateEnergyAssumptions.lean` to create an explicit intermediate hypothesis slot “energy/structure ⇒ near μ-Carleson”, with a helper theorem that combines a near bound with a far-regime Carleson bound to yield `OscillationTargetTail`.
- **Iteration 21 (explicit “choose K” lemma)**: strengthened `GeometricTail.lean` with `exists_pow_half_mul_le`, a direct Lean lemma encoding the engineering step “pick \(K\) so the geometric tail is below a target \(\varepsilon\)”.
- **Iteration 22 (B2′ constant chase as a theorem)**: added `RiemannRecognitionGeometry/OscillationTargetTailChase.lean`, which packages the “pick \(K\)” engineering step into a single theorem `oscillationTargetTail_of_decay`. This cleanly separates the deep analytic estimate (prove a geometric decay bound on mean oscillation) from the constant chase.
- **Iteration 23 (annulus-tail + Route‑A composition layer)**: added `RiemannRecognitionGeometry/AnnulusTailScaffold.lean` (generic “sum annuli ⇒ geometric tail” closure) and `RiemannRecognitionGeometry/MuCarlesonToTailDecay.lean` (explicit composition `μ‑Carleson ⇒ annulus majorant ⇒ TailMeanOscDecay ⇒ choose K ⇒ OscillationTargetTail`), and rewired `AssumptionsTail.lean` to use this composed bridge.

---

### 8) References (internal)

- `recognition-geometry-dec-18.tex`: current paper-facing B1/B2′/driver narrative.
- `renormalized_tail_bound.md`: detailed obstruction analysis + μ-Carleson discussion + height-dependent substitutes.
- `RiemannRecognitionGeometry/ExplicitFormula/`: Route-3 algebra + bridge interfaces.


