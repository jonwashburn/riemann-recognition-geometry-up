### Route‑3 Positivity Bridge (RH‑Equivalent Core): RS Passivity → Carathéodory/Herglotz → \(\mu \ge 0\)

This document isolates the **only RH‑equivalent step** in the Route‑3 program:

- from the identity/bookkeeping representation
  \[
  W^{(1)}(\mathrm{pair}(f,g))=\langle \nu,\overline{F_f}\,F_g\rangle
  \]
  (a signed/complex boundary distribution \(\nu\)),
- to a **positive** spectral measure
  \[
  W^{(1)}(\mathrm{pair}(f,g))=\int_{\mathbb R}\overline{F_f(t)}\,F_g(t)\,d\mu(t),
  \qquad \mu \ge 0.
  \]

Everything in `ROUTE3_IDENTITY_PART.md` is “hard but standard analysis.” This file is where RH “takes its last stand”: **\(\mu\ge0\)**.

---

### What positivity must mean (minimal classical form)

Let \(\mathcal T\) be the chosen test space (e.g. log‑Schwartz), and let \(F_f\) denote its boundary transform on the critical line.

Define the sesquilinear form:

\[
B(f,g) \;:=\; W^{(1)}(\mathrm{pair}(f,g)).
\]

#### Target positivity statement (Bochner-ready)

- **(Pos) Positive semidefinite**: for all \(f\in\mathcal T\),
  \[
  B(f,f) \in \mathbb R,\qquad B(f,f)\ge0.
  \]

If we also have the mild regularity/continuity needed to apply Bochner/Schwartz (see below), then (Pos) implies a **positive spectral measure** representation.

**RH equivalence:** in the Lagarias/Weil criterion, (Pos) for the ζ/ξ‑derived \(W^{(1)}\) is equivalent to RH (this is exactly Lagarias Thm 3.2 packaged in `LagariasFramework.weilPositivity`).

So: proving (Pos) for the arithmetic \(B\) is *the* unconditional breakthrough.

---

### Two equivalent classical “bridges” to \(\mu \ge 0\)

Both routes below are standard theorems in analysis; the RH‑equivalent work is showing that **the arithmetic ξ/ζ channel satisfies the hypotheses**.

#### Bridge A (Bochner / Wiener–Khintchine on \(\mathbb R\))

**Input hypotheses (typical):**
- **(B1) Positivity**: \(B(f,f)\ge0\) for all \(f\).
- **(B2) Hermitian**: \(B(g,f)=\overline{B(f,g)}\).
- **(B3) Translation invariance** in log‑time: \(B(\tau_a f,\tau_a g)=B(f,g)\) for the shift action \((\tau_a f)(x)=f(x-a)\).
- **(B4) Continuity**: \(B\) is continuous on the chosen Schwartz/test topology (so it defines a tempered distribution kernel).

**Conclusion (Bochner–Schwartz):**
There exists a **positive** Borel measure \(\mu\) of at most polynomial growth such that
\[
B(f,g)=\int_{\mathbb R}\overline{\widehat f(t)}\,\widehat g(t)\,d\mu(t),
\]
where \(\widehat f\) is the Fourier transform (the log‑Mellin boundary transform).

**Where RH hides:** for the actual ξ/ζ Weil form, (B1) is RH‑equivalent. (B3)+(B4) are “work,” but plausibly standard once the test space is chosen well (log‑Schwartz makes these natural).

#### Bridge B (Carathéodory/Herglotz on a half-plane or disk)

This is the “positive‑real transfer function” formulation (closest to passivity).

**Carathéodory/Herglotz theorem (standard):**
If \(\Phi\) is analytic on the right half‑plane \(\Re z>0\) and \(\Re\Phi(z)\ge0\) there, then \(\Phi\) admits a Herglotz representation with a **positive** boundary measure \(\mu\) on \(\mathbb R\) (Poisson extension of \(\mu\)).

**Route‑3 wrapper choice:**
Set
\[
\Phi(z)\;:=\; -\frac{\xi'}{\xi}\!\left(\tfrac12+z\right)
\quad\text{(or a closely related completed-channel field)}.
\]

**Conclusion:** \(\Re\Phi\ge0\) on \(\Re z>0\) produces a positive boundary measure \(\mu\).

**Where RH hides:** \(\Re\Phi(z)\ge0\) on \(\Re z>0\) is essentially equivalent to “no ξ‑zeros with \(\Re(s)>\tfrac12\)” (i.e. RH‑level content). This is why the “passivity” statement must carry real mathematical weight.

#### Splice option: import the positivity from the boundary-certificate manuscript

The boundary-certificate route (see `Riemann-active.txt`) constructs the explicit ratio
\[
\mathcal J(s)=\frac{\det_2(I-A(s))}{\mathcal O(s)\,\xi(s)},\qquad F(s)=2\mathcal J(s),
\]
and proves the a.e. **boundary wedge** \((\mathrm P^+)\): \(\Re F(\tfrac12+it)\ge0\) a.e., then pushes it into \(\Omega\) by Poisson
and globalizes by the Schur–Herglotz pinch. In other words, it supplies exactly the “positive‑real / passivity” hypothesis that Route‑3
otherwise treats as RH‑equivalent input.

Given \(\Re F\ge0\) on \(\Omega\), the remaining step “positive‑real ⇒ positive boundary measure” is classical (Herglotz/Nevanlinna).
The certificate route also produces an explicit candidate spectral boundary measure via the phase–velocity identity
(\(-w'=\pi\,\mu+\pi\sum m_\gamma\delta_\gamma\) in the notation of `Riemann-active.txt`), so \(\mu\ge0\) is automatic.

**Honest caveat (still needed for Route‑3):** this splice supplies the **sign** input (\(\mu\ge0\)), but it does not by itself prove the
Route‑3 **spectral identity** identifying the Lagarias/Weil form \(W^{(1)}\) with an \(L^2(\mu)\) pairing. That identification is the
“identity part” documented in `ROUTE3_IDENTITY_PART.md`.

---

### RS (Recognition Science) interpretation: what must be proven

In RS terms, this step is:

- **Passivity / no negative work** for the prime/ξ channel under the RS \(J\)-cost.
- Passivity ⇒ positive‑real response ⇒ positive spectral measure (power spectrum) ⇒ reflection positivity.

The RS→classical translation must therefore output one of the following:

- **(T1)** A direct proof of (Pos) for the arithmetic \(B\) on the chosen test class (Bochner route), or
- **(T2)** A proof that the chosen analytic response field \(\Phi\) is Carathéodory/positive‑real on \(\Re z>0\) (Herglotz route).

Either one is RH‑equivalent for the ξ/ζ field, so it is not “just work.”

---

### Lean-facing target (what to package as the single “bridge lemma”)

After the measure-first refactor, the clean Lean target is:

- produce a `SesqMeasureIdentity` for the ζ/ξ‑derived `W1`, with **positive** measure `μ`,
- then the existing `ReflectionPositivityRealization → WeilGate → RH` plumbing fires.

Concretely, the RH‑equivalent Lean lemma should look like:

- **BridgeLemma**: “(RS passivity / positive‑real / kernel positivity) ⇒ there exists `μ ≥ 0` such that
  \[
  W¹(\mathrm{pair}(f,g)) = \int \overline{F_f}\,F_g\,d\mu
  \]
  for all test functions.”

This can be implemented either:

- via **Bochner** (positivity + translation invariance ⇒ positive measure), or
- via **Carathéodory/Herglotz + GNS** (positive‑real ⇒ positive kernel ⇒ Hilbert realization).

---

### What remains to do (in this repo)

- **(Next doc)** Specify a single sharpened “BridgeLemma” statement with:
  - exact domain (half-plane vs disk),
  - exact positivity notion (Bochner PSD vs Carathéodory \(\Re\Phi\ge0\)),
  - exact regularity assumptions needed for the representing measure,
  - explicit note: which assumptions are standard and which are RH‑equivalent.
- **(Lean alignment)** Map this BridgeLemma to the current bridge point in
  - `RiemannRecognitionGeometry/ExplicitFormula/CayleyBridge.lean`
  (or replace it with a measure-first bridge statement).


