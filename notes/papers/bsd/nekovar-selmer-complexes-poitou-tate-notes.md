### Nekovář Selmer complexes / Poitou–Tate / Cassels–Tate — BSD audit notes

- **Citation**: Nekovář (Selmer complexes), plus standard PT references.
- **One-line relevance**: supplies “B3” and is central to `lemC:height=PT` and `thm:sha-finite`.

#### Results to extract
- **R1 (PT exact sequences)**: exact triangles/long exact sequences relating global cohomology, local conditions, and Selmer groups.
- **R2 (pairings)**: local Tate pairings and the global Poitou–Tate pairing; orthogonal complements and dimension formulas.
- **R3 (Cassels–Tate)**: relationship to \(\Sha[p^\infty]\) and when nondegeneracy implies finiteness/corank statements (careful: Appendix C.3 mistake).

#### Mapping to the proof track
- `B3`
- `lemC:height=PT`
- `thm:sha-finite` (all steps)

---

### What `thm:sha-finite` needs from PT (concrete checklist)

The source’s Step 1–Step 3 are only audit-grade if we can cite/derive the following PT/Selmer-complex facts **with the same local conditions** as the paper (ordinary or signed at \(p\), finite away from \(p\)):

#### (PT1) Exact Selmer complex description
- A definition of the Selmer complex \(R\Gamma_f(\mathbb{Q},V)\) (or \(R\Gamma_f(\mathbb{Q},T)\)) whose \(H^1\) is the Bloch–Kato/Greenberg Selmer group, matching the paper’s local conditions.

#### (PT2) Global duality / pairing
- A perfect pairing (Poitou–Tate) relating \(R\Gamma_f(\mathbb{Q},V)\) and its dual, yielding:
  - the Cassels–Tate pairing on \(\Sha[p^\infty]\),
  - and an orthogonality relationship between Kummer images and “dual Selmer” pieces.

#### (PT3) “Orthogonal ⇒ torsion” mechanism (the missing lemma)
The paper’s Step 3 claims:
> if \(x\in \mathrm{Sel}_\chi\) is orthogonal to \(\kappa(E(\mathbb{Q})\otimes\mathbb{Q}_p)\), then \(x\) lies in the intersection of local kernels at all places, hence is torsion.

To make this rigorous we need an explicit statement of the form:
- if \(x\) pairs trivially against all Kummer classes under the specialized height pairing, then \(x\) lies in the **nullspace** of the height pairing;
- then (HΛ)(ii) forces \(\mathrm{loc}_p x\) into the χ-local condition kernel;
- and PT identifies the remaining local constraints (away from \(p\)) so that the only such classes are torsion / finite.

This is the key place where the paper must differ from Appendix C.3’s incorrect “orthogonal complement is zero” argument; the exact PT statement used here should be extracted carefully.

#### (PT4) Fixed-prime finiteness vs global finiteness
- Even if PT implies \(\mathrm{corank}_{\mathbb{Z}_p}\Sha[p^\infty]=0\) for each \(p\), PT does **not** by itself imply only finitely many primes contribute. A separate argument is needed to pass to global finiteness of \(\Sha\).

---

### Extracted target statements (draft; to cite precisely)

The point of this section is to turn the checklist above into **theorems we can actually cite** inside the `BSD_Jon_Final_PROOF_TRACK.md` proof of `thm:sha-finite`.

#### PT1 — Selmer complex encodes the Selmer group (definition + identification)

Let \(T\) be a free \(\mathbb{Z}_p\)-representation of \(G_{\mathbb{Q}}\) (e.g. \(T=T_pE\)) and \(V=T\otimes_{\mathbb{Z}_p}\mathbb{Q}_p\). Fix a Selmer structure \(F\) consisting of local conditions \(H^1_F(\mathbb{Q}_v,V)\subset H^1(\mathbb{Q}_v,V)\) (in our case: **ordinary/signed at \(p\)**, **finite** away from \(p\)).

Then there is a Selmer complex \(R\Gamma_F(\mathbb{Q},V)\) (Nekovář) such that:
- \(H^1(R\Gamma_F(\mathbb{Q},V))\) identifies with the (Bloch–Kato/Greenberg) Selmer group \(\mathrm{Sel}_F(\mathbb{Q},V)\).
- The cohomology long exact sequence of \(R\Gamma_F\) recovers the familiar “global \(H^1\) with local conditions” exact sequence:
  \[
    0\to \mathrm{Sel}_F(\mathbb{Q},V)\to H^1(\mathbb{Q},V)\to \bigoplus_v H^1(\mathbb{Q}_v,V)/H^1_F(\mathbb{Q}_v,V)\to \cdots
  \]

**To cite**: Nekovář, *Selmer complexes*, Selmer complex construction + identification of \(H^1\) with Selmer (exact theorem/prop number TBD).

#### PT2 — Poitou–Tate duality for Selmer complexes (pairing + orthogonality)

Let \(T^*:=\mathrm{Hom}(T,\mathbb{Z}_p)(1)\) and let \(F^*\) be the dual Selmer structure (orthogonal complements under local Tate pairings).

Then Poitou–Tate duality gives a canonical perfect pairing in the derived category that induces (on cohomology) perfect pairings
\[
H^i(R\Gamma_F(\mathbb{Q},T))\times H^{3-i}(R\Gamma_{F^*}(\mathbb{Q},T^*))\longrightarrow \mathbb{Q}_p/\mathbb{Z}_p,
\]
and, in particular, identifies orthogonal complements of global Selmer classes with dual Selmer quotients.

**Operational corollary (what the proof track needs)**: there is a **Cassels–Tate style pairing** on \(\Sha(E/\mathbb{Q})[p^\infty]\) (or on a quotient by divisible subgroups) induced from PT, and “local-kernel intersection” conditions can be recognized as belonging to torsion/divisible Sha-parts.

**To cite**: Nekovář *Selmer complexes* (global duality theorem) and/or a standard PT reference (exact theorem/prop number TBD).

#### PT3 — Height pairings as PT pairings with Bockstein (radical control mechanism)

In Nekovář’s framework, the (cyclotomic) \(p\)-adic height pairing on (an extended) Selmer group is constructed from:
- the global Poitou–Tate pairing, and
- a Bockstein/derivative operator coming from the cyclotomic deformation.

Concretely, one expects a formula of the schematic form
\[
h(x,y)=\langle x,\ \beta(y)\rangle_{\mathrm{PT}},
\]
where \(\langle\cdot,\cdot\rangle_{\mathrm{PT}}\) is a PT pairing (valued in \(\mathbb{Q}_p\) after choosing splittings) and \(\beta\) is the cyclotomic Bockstein map.

**What `thm:sha-finite` needs** is the following *referee-grade lemma*:

> (**PT3 target lemma**) Let \(\mathrm{Sel}_\chi\) be the χ-specialized Selmer group equipped with the χ-specialized height \(h_\chi\).  
> Assume \(h_\chi\) is nondegenerate on \(\mathrm{Sel}_\chi/\mathrm{tors}\) and that any \(x\in\mathrm{Sel}_\chi\) orthogonal to the Kummer image \(\kappa(E(\mathbb{Q})\otimes\mathbb{Q}_p)\) must lie in the PT-defined “local-kernel intersection” subgroup (equivalently: the radical/nullspace predicted by Nekovář’s height formalism).  
> Then \(\dim_{\mathbb{Q}_p}\mathrm{Sel}_\chi=\mathrm{rank}\,E(\mathbb{Q})\).

This is exactly the missing bridge between “height nondegeneracy on Selmer” and “no extra Selmer classes beyond Mordell–Weil”.

**To cite**: Nekovář (construction of \(p\)-adic heights via Selmer complexes + Bockstein + PT), plus a lemma identifying the radical with the relevant Sha/local-kernel intersection subgroup (exact citations TBD).

#### PT4 — Fixed-prime finiteness vs global finiteness (explicit warning lemma)

Even if one can prove for every prime \(p\) that \(\Sha(E/\mathbb{Q})[p^\infty]\) is finite, it does **not** follow formally that \(\Sha(E/\mathbb{Q})\) is finite: the direct sum \(\bigoplus_p \Sha[p^\infty]\) can still be infinite if infinitely many primes contribute nontrivially.

**What the proof track needs** is an additional global lemma of the form:
- “\(\Sha[p^\infty]=0\) for all but finitely many \(p\)”, or
- “\(\Sha\) has bounded exponent / bounded order”, or
- an independent global argument implying \(\Sha\) is finite.



