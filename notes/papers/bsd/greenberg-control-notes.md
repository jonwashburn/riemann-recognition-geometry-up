### Greenberg ordinary local conditions + control (1989+) — BSD audit notes

- **Citation**: Greenberg (1989) and later standard control theorem references.
- **One-line relevance**: supplies “B4” and parts of the (HΛ) → Selmer dimension arguments.

#### Results to extract
- **R1 (ordinary local condition)**: definition and properties of the ordinary local condition at \(p\) in \(H^1(\mathbb{Q}_p,V)\) / Iwasawa cohomology.
- **R2 (control theorem)**: comparison of Selmer groups over \(\mathbb{Q}\), \(\mathbb{Q}_\infty\), and χ-specializations; exact hypotheses and finite-error terms.
- **R3 (finite local conditions away from \(p\))**: how they enter PT exact sequences and Selmer complexes.

#### Mapping to the proof track
- `B4`
- `thm:sha-finite` Step 4 (χ-specializations → cyclotomic base)
- operator model construction (`thm:coker-id`) implicitly uses “Selmer local conditions packaged into \(\Phi=(\mathrm{Col}_p,\pi)\)”

---

### What `thm:sha-finite` needs from “control” (concrete checklist)

The source’s Step 4 claims (schematically):
\[
\dim_{\mathbb{Q}_p}\mathrm{Sel}_\chi=\mathrm{rank}\,E(\mathbb{Q})\quad\Rightarrow\quad
\mathrm{corank}_{\mathbb{Z}_p}\mathrm{Sel}_{p^\infty}(E/\mathbb{Q})=\mathrm{rank}\,E(\mathbb{Q}).
\]

To make this audit-grade we need:

#### (C1) Exact definition of χ-specialized Selmer
- A precise definition of \(\mathrm{Sel}_\chi\) as the χ-eigenspace / specialization of an Iwasawa Selmer object, and how it relates to the classical Selmer group over \(\mathbb{Q}\) or over finite layers.

#### (C2) Bounded kernel/cokernel control statement
- A theorem matching the paper’s standing hypothesis `\eqref{eq:control}`: the control maps have bounded kernel/cokernel, uniformly in the cyclotomic layer and compatible with χ-specialization.

#### (C3) Dimension/corank comparison lemma
- A lemma that turns the χ-level \(\mathbb{Q}_p\)-dimension statement into a \(\mathbb{Z}_p\)-corank statement for the \(p^\infty\)-Selmer group over \(\mathbb{Q}\).

#### (C4) Edge cases
- Ordinary vs signed supersingular control hypotheses.
- Exceptional zero / split multiplicative cases (if included).

---

### Extracted target statements (draft; to cite precisely)

#### C1 — χ-specialized Selmer objects (definition + identification)

Let \(\mathbb{Q}_\infty/\mathbb{Q}\) be the cyclotomic \(\mathbb{Z}_p\)-extension with \(\Gamma=\mathrm{Gal}(\mathbb{Q}_\infty/\mathbb{Q})\) and \(\Lambda=\mathbb{Z}_p\llbracket \Gamma\rrbracket\). Let \(T=T_pE\), \(V=T\otimes \mathbb{Q}_p\).

Fix a Selmer structure \(F\) (ordinary at \(p\) / finite away from \(p\), or signed at supersingular \(p\)). Let \(\mathrm{Sel}_F(\mathbb{Q}_\infty,T)\) be the corresponding Iwasawa Selmer group and \(X:=\mathrm{Sel}_F(\mathbb{Q}_\infty,T)^\vee\) its Pontryagin dual (a compact \(\Lambda\)-module).

For a finite-order character \(\chi:\Gamma\to \overline{\mathbb{Q}}_p^\times\), define the χ-specialization/eigenspace Selmer object by one of the equivalent models:
- \(X\otimes_{\Lambda,\chi}\mathbb{Z}_p\) (algebraic specialization), or
- \(\mathrm{Sel}_F(\mathbb{Q},V(\chi^{-1}))\) (classical Selmer for the χ-twist), via evaluation of Iwasawa cohomology.

**What to cite**: a reference identifying χ-specialization of Iwasawa cohomology/Selmer with the classical Selmer group of the twisted representation (exact lemma/theorem TBD; often treated as standard in Iwasawa cohomology texts).

#### C2 — Greenberg control (bounded kernel/cokernel)

Assume \(E/\mathbb{Q}\) has good ordinary reduction at \(p\) (and the ordinary local condition at \(p\) is used). Let \(\mathbb{Q}_n\) be the \(n\)-th finite layer of \(\mathbb{Q}_\infty\).

Then the natural restriction/control maps
\[
\mathrm{Sel}_F(\mathbb{Q}_n,T)\ \longrightarrow\ \mathrm{Sel}_F(\mathbb{Q}_\infty,T)^{\Gamma_n}
\]
have **finite kernel and cokernel**, and under standard hypotheses (no “exceptional” local phenomena) these sizes are bounded independently of \(n\).

**What the proof track uses**: boundedness of these error terms is exactly the standing black box `eq:control` (“B4”) referenced in `BSD-Jon-Final.txt`.

**To cite**: Greenberg (1989) control theorem for ordinary Selmer, or a modern reference (exact theorem number TBD).

#### C3 — Dimension/corank comparison (χ-level → \(p^\infty\)-level)

Let \(M\) be a cofinitely generated \(\mathbb{Z}_p\)-module. Then
\[
\mathrm{corank}_{\mathbb{Z}_p}(M)=\dim_{\mathbb{Q}_p}(M\otimes_{\mathbb{Z}_p}\mathbb{Q}_p).
\]

In particular, for the classical \(p^\infty\)-Selmer group \(\mathrm{Sel}_{p^\infty}(E/\mathbb{Q})\),
\[
\dim_{\mathbb{Q}_p}\big(\mathrm{Sel}_{p^\infty}(E/\mathbb{Q})\otimes \mathbb{Q}_p\big)
=\mathrm{corank}_{\mathbb{Z}_p}\mathrm{Sel}_{p^\infty}(E/\mathbb{Q}).
\]

So if one can identify the χ=trivial specialization \(\mathrm{Sel}_\chi\) with \(\mathrm{Sel}_{p^\infty}(E/\mathbb{Q})\otimes\mathbb{Q}_p\) (or with the Bloch–Kato/Greenberg \(V\)-Selmer group), then a dimension computation at χ=1 directly yields the corank identity used in Step 4 of `thm:sha-finite`.

#### C4 — Signed supersingular / exceptional cases

The signed (\(\pm\)) theory replaces the ordinary local condition at \(p\) by \(\pm\)-local conditions (Kobayashi/Pollack/LLZ). The control theorem and specialization statements need to be checked separately in those cases; the proof track should treat them as conditional unless explicit references are imported.



