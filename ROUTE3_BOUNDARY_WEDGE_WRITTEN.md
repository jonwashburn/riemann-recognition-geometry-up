### Goal (Step 2 / Recognition Geometry / “boundary wedge”)

Prove **boundary positivity** `(P+)` for the ζ pinch field, i.e.

- **(P+)**: for the PSC ratio \(J(t)\) on the critical line,
  \[
  \text{for a.e. } t\in\mathbb{R},\quad \Re\bigl(2\,J(1/2+it)\bigr)\ge 0.
  \]

In the codebase this is expressed as `PPlus_zeta` (see `PPlusZeta.lean`).

### Immediate reduction: phase → cosine

Assume the **boundary phase representation** (already present as `ZetaPSCHypotheses.boundaryPhase_repr`):

- **Phase repr**: for a.e. \(t\),
  \[
  J(1/2+it)=\exp(i\,\theta(t)).
  \]

Then we have the identity
\[
\Re\bigl(2\,\exp(i\theta(t))\bigr)=2\cos(\theta(t)).
\]

So:

- **(P+) ⇔ cosine nonneg**:
  \[
  (P+) \iff \text{for a.e. }t,\ \cos(\theta(t))\ge 0.
  \]

This equivalence is proved formally in:

- `RiemannRecognitionGeometry/ExplicitFormula/PPlusCore.lean`
- specialized to ζ in `RiemannRecognitionGeometry/ExplicitFormula/PPlusZeta.lean`

So the entire “phase argument” becomes one target statement:

- **Target**: `∀ᵐ t, 0 ≤ Real.cos (boundaryPhase t)`.

### Boundary wedge mechanism (what is actually hard)

We now explain what must be proved to get \(\cos(\theta(t))\ge 0\) a.e.

The `riemann-finish` pipeline (`rh/RS/BoundaryWedgeProof.lean`) proceeds in 3 conceptual moves:

#### A. Lower bound (phase–velocity / Poisson plateau)

For each Whitney interval \(I\) (center \(t_0\), half-length \(L\)), define a “windowed phase integral”
\[
\mathrm{WP}(I) := \int_{t\in I}\psi_I(t)\,\theta'(t)\,dt
\]
or an equivalent CR–Green boundary integral (implementation-dependent).

Prove a **Poisson plateau inequality**:
\[
c_0\cdot \mathrm{pb}(I)\ \le\ |\mathrm{WP}(I)|
\]
where \(\mathrm{pb}(I)\) is the Poisson balayage/harmonic measure of \(I\) seen from a canonical interior
point above \(I\).

This step typically uses:

- a **phase–velocity identity** decomposing \(\mathrm{WP}(I)\) into a Poisson term plus residues/atoms;
- **nonnegativity of atoms** (residue / winding number positivity);
- an explicit lower bound constant \(c_0\) for the Poisson plateau (depends on the window \(\psi\)).

In `riemann-finish`, the relevant named theorem is `phase_velocity_lower_bound`.

#### B. Upper bound (CR–Green + Carleson/Whitney energy)

Prove an upper bound on the same windowed phase:
\[
|\mathrm{WP}(I)| \ \le\ C_\psi \sqrt{\mathrm{CarlesonEnergy}(I)}
\]
and then show a **uniform Carleson budget**:
\[
\mathrm{CarlesonEnergy}(I)\ \le\ K_\xi\cdot (2L).
\]

So overall:
\[
|\mathrm{WP}(I)| \ \le\ C_\psi\sqrt{K_\xi\cdot(2L)}.
\]

This is the analytic “energy control” part. In `riemann-finish` it is named as
`whitney_phase_upper_bound`, and its sub-ingredients mention VK / zero-density / counts.

#### C. Wedge closure + Whitney upgrade to a.e. boundary positivity

Combine the bounds:

\[
c_0\cdot \mathrm{pb}(I)\ \le\ |\mathrm{WP}(I)|\ \le\ C_\psi\sqrt{K_\xi\cdot(2L)}.
\]

This yields a **wedge inequality** on each Whitney interval.

Then prove a local “integral nonnegativity implies a.e. pointwise nonnegativity” step on each interval,
and finally a **Whitney covering lemma** that upgrades:

- wedge bound on all Whitney intervals
  ⇒ boundary positivity holds **almost everywhere** on \(\mathbb{R}\).

This is the “covering theory + local-to-global” move.

### Minimal assumption bundle (as an interface)

In this repo, we package exactly the *minimal* remaining claims as the structure:

- `RiemannRecognitionGeometry/ExplicitFormula/BoundaryWedgeInterfaces.lean`
  - `BoundaryWedgeAssumptions`:
    - provides the **lower bound**, **upper bound**, and **Whitney upgrade** as named fields;
    - proves: `BoundaryWedgeAssumptions → PPlus_zeta → cos(boundaryPhase)≥0 a.e.`

And we expose a single “shim axiom” supplying that bundle:

- `RiemannRecognitionGeometry/ExplicitFormula/PPlusZetaShim.lean`
  - `axiom boundaryWedgeAssumptions_zeta : BoundaryWedgeAssumptions`

This is intentionally modular: we can replace individual fields with proofs one-by-one.

### What is “novel math” vs standard?

- **Standard / classical (but still substantial to formalize)**:
  - Whitney decomposition / covering arguments (harmonic analysis)
  - Green’s identities / Cauchy–Schwarz energy bounds (PDE / functional analysis)
  - residue theorem / winding number positivity
  - Poisson kernel facts and transport

- **RH-specific / potentially novel**:
  - the *exact* choice of the CR–Green “field” whose boundary trace is your PSC ratio,
    and the exact identification of the phase integrand with that boundary trace;
  - obtaining a **numerically small enough** Carleson/energy constant \(K_\xi\) (e.g. via VK zero-density)
    that makes the wedge closure constants work;
  - ensuring all constants interlock to give the decisive “wedge closure” inequality.

### Recommendation

Yes: **write this step in clean paper form first** (with explicit hypotheses and citations),
because Lean needs:

- the exact definitions (what is \(\mathrm{WP}(I)\), what is the Carleson energy, what is the field),
- the exact dependency graph (what is assumed vs proved),
- and a stable statement of the endgame (wedge bounds ⇒ a.e. positivity ⇒ interior positivity).

The current code now matches that: the paper proof can be written by walking the fields of
`BoundaryWedgeAssumptions` and then progressively discharging them.


