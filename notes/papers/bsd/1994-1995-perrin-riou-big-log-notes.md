### Perrin–Riou explicit reciprocity / big logarithm (1994/1995) — BSD audit notes

- **Citation**:
  - Perrin–Riou, *Fonctions L p-adiques des représentations p-adiques* (1995) and related 1994 preprints.
  - Wach-module implementations/modern treatments: Berger (2003), Cherbonnier–Colmez (1999).
- **One-line relevance**: supplies the χ-specialization/interpolation that the paper packages as `lem:PR-ord-proof` / `lem:PR-signed-proof`.

#### Results to extract (target statements)
- **R1 (ordinary interpolation)**: evaluation of \(\mathcal{L}_V\) at a finite-order cyclotomic character χ recovers Bloch–Kato logarithm/exponential maps (up to explicit Euler factors), and after projecting to the ordinary/unit-root line those factors are \(p\)-adic units away from a finite exceptional set.
  - **Used by**: `lem:PR-ord-proof`, `thm:HL-ordinary`, `lem:triang-ord-modp`.
- **R2 (signed interpolation)**: same statement with signed projectors/logarithms \(\log^\pm\) and signed Coleman maps, with unit factors \(u_\pm(E,p,\chi)\in\mathbb{Z}_p^\times\).
  - **Used by**: `lem:PR-signed-proof`, `thm:HL-signed`, `lem:triang-signed`.
- **R3 (integrality / \(\Lambda\)-linearity)**: \(\mathcal{L}_V\) is \(\Lambda\)-linear on \(H^1_{\mathrm{Iw}}(\mathbb{Q}_p,V)\) and respects Wach lattices so the resulting Coleman maps have coefficients in \(\Lambda\).
  - **Used by**: operator model sections and determinant identities.

#### Assumptions / caveats to pin down
- **Ordinary vs supersingular**: which variant of Perrin–Riou/Wach theory is being invoked.
- **Exceptional zeros**: identify the finite set of χ for which the “unit factor” fails, and how the paper excludes/corrects it.
- **Normalizations**:
  - choice of Néron differential \(\omega\),
  - choice of ordinary projector \(e_{\mathrm{ord}}\) or signed projectors \(e_\pm\),
  - normalization of \(\mathcal{L}_V\) (branch choice),
  - definition of the Coleman map \(\mathrm{Col}_p\) in the paper vs the reference.

#### Mapping to this repo’s proof track
- **Primary labels**:
  - `lem:PR-ord-proof` (ordinary reciprocity)
  - `lem:PR-signed-proof` (signed reciprocity)
  - `thm:HL-ordinary`, `thm:HL-signed` ((HΛ) theorems)
  - `lem:triang-ord-modp`, `lem:triang-signed` (mod‑\(p\) height congruences)

#### What would still be missing (even after we import R1/R2/R3)
- An audit-grade reference for **nondegeneracy** of the specialized Bloch–Kato height on \(E(\mathbb{Q})\otimes\mathbb{Q}_p\) modulo torsion (the proof track currently treats this as conditional).
- A normalization reconciliation for the **formal-group valuation** issue (§7.1 vs unit-diagonal claims).

#### Next actions
- **Extract**: exact theorem statements from a specific modern reference (likely Berger/LLZ exposition) with hypotheses spelled out.
- **Specify**: the precise dictionary between \((\ell\circ \mathcal{L}_V)(\chi)\) and \(\mathrm{Col}_p(\chi)\), and between that and the Bloch–Kato logarithm used in the paper.



