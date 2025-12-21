### Coleman–Gross \(p\)-adic heights (cyclotomic) — BSD audit notes

- **Citation**: Coleman–Gross (original \(p\)-adic height), plus modern treatments (Nekovář, Perrin–Riou, Besser/Coleman integration references as needed).
- **One-line relevance**: this is the “B2” black box: it fixes what \(h_p\) is, its integrality, and the formal-group factorization/normalization that currently produces the §7.1 contradiction.

#### Results to extract
- **R1 (definition + bilinearity + symmetry)**: the local cyclotomic height pairing \(h_p(\cdot,\cdot)\) with Greenberg local conditions, and the global height/regulator story.
- **R2 (formal group factorization)**: on \(E_1(\mathbb{Q}_p)\), \(h_p(X,Y)=u_p\log_E(X)\log_E(Y)\) with explicit normalization of \(u_p\) and \(\log_E\).
- **R3 (integrality)**: criteria for \(h_p(P)\in\mathbb{Z}_p\) and valuation comparisons with \(\log_\omega(P)\) on integral points.
- **R4 (comparison with Bloch–Kato heights)**: identify the specialized Bloch–Kato height with Coleman–Gross height (up to a unit) under ordinary/signed hypotheses.

#### Assumptions / caveats
- Which local conditions are used (ordinary, finite, signed).
- Normalizations: Néron differential, local parameter \(t\), Coleman branch.
- Exceptional zero corrections (if any) and their effect on unit factors.

#### Mapping to the proof track
- `B2`, `lem:formal-factor`, `lem:unit-log`, `lem:diag-units`
- Appendix C / PT comparison (`lemC:height=PT`)

#### Critical audit question
- Resolve the normalization mismatch: under the stated §7.1 expansion \(t(X)\in p\mathbb{Z}_p\) and \(\log_E(T)=T+O(T^2)\), formal-group points have \(\log_E(X)\in p\mathbb{Z}_p\), so diagonal heights have \(v_p\ge 2\).  
  If the paper wants “unit diagonals” on formal-group points, some normalization must differ (e.g. a \(p^{-1}\)-rescaled log or different parameter choice).

---

### What the *source file* commits to (internal evidence)

These are **internal commitments** in `BSD-Jon-Final.txt` that any Coleman–Gross normalization must satisfy.

#### (S1) Regulator normalization is unscaled
In §2.4, the paper defines the cyclotomic \(p\)-adic regulator as
\[
\mathrm{Reg}_p(E):=\det(h_p(P_i,P_j))_{1\le i,j\le r}
\]
for a \(\mathbb{Z}\)-basis \(\{P_i\}\) of \(E(\mathbb{Q})/\mathrm{tors}\) (`BSD-Jon-Final.txt` L162–L170).

So there is **no built-in \(p^{-2r}\)** scaling that would automatically turn “valuation 2 on every diagonal” into a unit regulator.

#### (S2) §7.1 asserts a height formula on the formal group with a unit prefactor
§7.1 asserts:
- for \(X\in E_1(\mathbb{Q}_p)\), \(t(X)\in p\mathbb{Z}_p\) (`BSD-Jon-Final.txt` L2408),
- \(\log_E(T)=T+O(T^2)\) with \(\log_E(T)\in \mathbb{Z}_p\llbracket T\rrbracket\) (L2400–L2403),
- and for ordinary \(p\) with no exceptional zero,
  \[
  h_p(X)=u_p\bigl(\log_E(t(X))\bigr)^2,\qquad u_p\in\mathbb{Z}_p^\times
  \]
  (L2411–L2414, citing `lem:formal-factor`).

These imply:
\[
\log_E(t(X))\in p\mathbb{Z}_p \;\Rightarrow\; v_p(\log_E(t(X)))\ge 1 \;\Rightarrow\; v_p(h_p(X))\ge 2,
\]
so **diagonal heights of formal-group points cannot be \(p\)-adic units** under the §7.1 formula as written.

#### (S3) §7.1 “expected outcome” is inconsistent as written
§7.1 then states the “expected outcome”:
“for all but finitely many ordinary \(p\), \(v_p(\log_E(t(mP)))=0\), so \(h_p(mP)\in\mathbb{Z}_p^\times\)” (L2417),
but this contradicts (S2) whenever \(mP\in E_1(\mathbb{Q}_p)\).

---

### Plausible minimal corrections (to be confirmed)

To salvage the intended “formal-group diagonal units” pipeline, **one** of the following must be true (or the pipeline must be abandoned):

1. **Scaled logarithm**: the paper’s “\(\log_p(X)\)” on \(E_1(\mathbb{Q}_p)\) is actually \(\log_E(t(X))/p\) (or equivalent), so it maps \(E_1\) into \(\mathbb{Z}_p\) with generic units; then the correct diagonal formula would be
   \[
   h_p(X)=u_p\Bigl(\frac{\log_E(t(X))}{p}\Bigr)^2,
   \]
   (or equivalently: the “\(u_p\)” in §7.1 secretly has valuation \(-2\)).
2. **Different “formal parameter” convention**: the parameter called \(t\) in §7.1 is not the standard Néron parameter with \(t(E_1)\subset p\mathbb{Z}_p\).
3. **The “expected outcome” is simply wrong**: in which case the advertised “height‑unit candidate” pipeline for \(r>1\) cannot work as stated and downstream unit‑regulator claims remain blocked.

Next step in this note: pin down which convention Coleman–Gross heights actually use (via external references) and reconcile it with the paper’s internal equations.


