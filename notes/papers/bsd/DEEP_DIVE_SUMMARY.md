### BSD external deep-dive summary (paper → proof-track dependencies)

This file is the **index** for the BSD proof-track external inputs.

Each row links:
- a **reference** (paper/book),
- what it supplies (precise theorem),
- which proof-track labels depend on it,
- and the current audit status.

#### Index

| Ref | What we need from it | Proof-track labels impacted | Status |
|---|---|---|---|
| Perrin–Riou (1994/1995) + Berger (2003) + Cherbonnier–Colmez (1999) | Big logarithm \(\mathcal{L}_V\) and explicit reciprocity / χ-interpolation (ordinary + signed variants) | `lem:PR-ord-proof`, `lem:PR-signed-proof`, `thm:HL-ordinary`, `thm:HL-signed`, `lem:triang-ord-modp`, `lem:triang-signed` | todo |
| Coleman–Gross (heights) + Nekovář | Definition/normalization of cyclotomic \(p\)-adic height; formal-group factorization; integrality | `B2`, `lem:formal-factor`, `lem:unit-log`, `lem:diag-units`, `lemC:height=PT` | **blocked (internal contradiction in §7.1 / Lemma `lem:unit-log` usage)** |
| Greenberg (1989) | Ordinary local conditions; control theorems; PT framework references | `B4`, `thm:sha-finite`, `thm:HL-ordinary`, operator model (`thm:coker-id`) | todo |
| Kato (2004) | One-sided divisibility / Euler system input (B1′) | `B1'`, `prop:mu-zero`, `prop:BSDp` | todo |
| Kobayashi (2003) + Pollack (2003) + LLZ (2012) | Signed local conditions, signed Coleman maps, signed heights/reciprocity | `thm:HL-signed`, `lem:PR-signed-proof`, `lem:triang-signed`, `lem:diag-units-signed` | todo |
| Nekovář (Selmer complexes) | Precise PT/Cassels–Tate pairing formalism, orthogonality statements | `B3`, `lemC:height=PT`, `thm:sha-finite` | todo |


