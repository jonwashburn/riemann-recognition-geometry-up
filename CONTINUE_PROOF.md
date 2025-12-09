# Riemann Hypothesis Recognition Geometry - Continuation Prompt

## Goal
Complete a fully unconditional Lean 4 proof of the Riemann Hypothesis using Recognition Geometry. No `sorry`s or custom axioms allowed.

## Current Status (Updated Dec 9, 2025)
- **Build**: ✅ Compiles successfully  
- **Sorries**: 3 sorry calls in 2 declarations
- **FeffermanStein.lean**: ✅ SORRY-FREE!

## Remaining Sorries (3 sorry calls, 2 declarations)

| Line | Declaration | Case | Blocker |
|------|-------------|------|---------|
| 903 | `phase_bound_from_arctan` | σ > b, γ > 0 | `nlinarith` on bound `1/3 ≤ (x-y)/(1+xy)` |
| 1128 | `phase_bound_neg_im` | σ ∈ [a,b], γ < 0 | `simp` failures, type mismatches |
| 1309 | `phase_bound_neg_im` | σ > b, γ < 0 | Same as line 903 |

## Technical Analysis

### σ > b Case (Lines 903, 1309)
The bound `(x-y)/(1+xy) ≥ 1/3` requires showing `1 + xy ≤ 3(x-y)`.

**Variables:**
- `x = (b-σ)/γ < 0`, `y = (a-σ)/γ < 0`, `x > y`
- `x - y = (b-a)/γ ≥ 1` (from `h_spread`)
- `xy = (b-σ)(a-σ)/γ² > 0`

**Available constraint:** `hσ_upper : ρ.re ≤ 1` (critical strip)

**Derived bounds:**
- `σ - b ≤ 1 - b ≤ 1 - γ` (since `b ≥ γ` from `hγ_upper`)
- `|x| = (σ-b)/γ ≤ (1-γ)/γ`

**Why `nlinarith` fails:** The inequality `xy ≤ 3(x-y) - 1` requires polynomial reasoning that `nlinarith` can't find with the available hypotheses. Need to manually derive intermediate bounds.

### Mixed-Sign Case (Line 1128)
For γ < 0 with σ ∈ [a, b]:
- `x = (b-σ)/γ ≤ 0` and `y = (a-σ)/γ ≥ 0`
- Need `|phaseChange| ≥ 4·arctan(1/5) > L_rec`

**Approach:** Use `phaseChange_abs_conj` to reduce to γ > 0 case.
**Blockers:**
1. `simp` not simplifying `starRingEnd` correctly
2. Type mismatches with `blaschkePhase_arctan` hypotheses
3. Edge case handling when σ = a or σ = b (singular points)

## Suggested Approach

1. **Add lemma hypotheses:** Explicitly require `a < σ < b` (strict) for mixed-sign case to avoid edge case issues.

2. **Use `polyrith` or `nlinarith` with explicit terms:** For σ > b case, may need to provide explicit intermediate bounds that nlinarith can use.

3. **Factor out reusable lemmas:** Create helper lemmas for the arctan bounds that can be proven separately.

## Build Commands

```bash
lake build 2>&1 | grep -E "error:|sorry"
grep -n "sorry" RiemannRecognitionGeometry/Axioms.lean
```

## Notes

- DirichletEta.lean being developed in separate session (`zero_has_nonzero_im`)
- FeffermanStein.lean is completely proven (with 5 axioms)
- The σ ≤ 1 constraint is now available in lemma signatures (recently added)
- All 3 remaining sorries have similar structure: arctan bounds from Whitney geometry
