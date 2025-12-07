# Phase Bound Fix Required

## Current Status: 9 sorries

The phase bound lemmas now have both lower and upper bound constraints:
- `h_width_lower : b - a ≥ |ρ.im|`  
- `h_width_upper : b - a ≤ 14 * |ρ.im|`

## Key Issue

The mixed-sign case in `phase_bound_from_arctan` (lines 442-516) relies on `phaseChange_arctan_formula`, which has a sorry for the mixed-sign case at line 243.

The formula `|phaseChange| = 2 * |arctan_diff|` is **incorrect** for the mixed-sign case. The correct formula is:
```
|phaseChange| = 2|π - Δ|  where Δ = arctan(x) + arctan(|y|)
```

## Required Fix

Instead of using `phaseChange_arctan_formula`, the mixed-sign case should prove directly:

1. Compute: `phaseChange = 2(arctan(γ/(a-σ)) - arctan(γ/(b-σ)))`
2. Use arctan reciprocal identities to get: `phaseChange = -2π + 2Δ`
3. So `|phaseChange| = 2(π - Δ)` when `Δ < π`
4. Bound Δ using upper constraint:
   - `x + |y| = (b-a)/γ ≤ 14`
   - `Δ ≤ 2*arctan((b-a)/(2γ)) ≤ 2*arctan(7)` (midpoint maximum)
   - `2*arctan(7) ≈ 2.856 < π - L_rec/2 ≈ 2.87`
5. Therefore `π - Δ ≥ L_rec/2`, so `|phaseChange| ≥ L_rec`

## Numerical Verification

For K = 14 (max ratio (b-a)/γ):
- arctan(7) ≈ 1.428
- 2*arctan(7) ≈ 2.856
- π - 2.856 ≈ 0.285
- 2 * 0.285 = 0.57 > L_rec ≈ 0.55 ✓

The upper bound constant K=14 is chosen to ensure this margin.
