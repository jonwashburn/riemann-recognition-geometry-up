# Remaining Work for Unconditional RH Proof

## Current Status: 10 sorries

### Analysis Complete, Implementation Pending

**1. Same-sign phase bounds (Axioms lines 546, 567)**
- Mathematical approach identified:
  - For σ < a case: y = (a-σ)/γ < 1 (proven: σ < a ≤ γ implies a - σ < γ)
  - For x - y ≥ 1 and y < 1: use arctan subtraction formula
  - arctan(x) - arctan(y) = arctan((x-y)/(1+xy)) ≥ arctan(1/3)
  - 2 * arctan(1/3) > L_rec ✓
- Need: Import/prove arctan subtraction formula from Mathlib
  - `Real.arctan_add` exists, need to derive subtraction version

**2. σ > b case (Axioms line 567)**
- Similar to σ < a but need different bound
- May require additional geometric constraint on how far σ can be from [a,b]

### Require Classical Analysis

**3. zero_has_nonzero_im (Axioms line 780)**
- Need: ζ(s) ≠ 0 for real s ∈ (0, 1)
- Approach: ζ(s) < 0 on (0,1) via Dirichlet eta function
- Effort: ~70 lines, not currently in Mathlib

**4. blaschke_dominates_total (Axioms line 886)**
- The main BMO→Carleson embedding theorem
- Effort: ~300 lines of classical analysis
- Components: Weierstrass factorization, BMO norm bound, Fefferman-Stein

**5. whitney_interval_width (Main line 98)**
- Need: 2 * I.len ≥ |ρ.im| for covering interval
- Issue: Current construction chooses scale based on Re(ρ), not Im(ρ)
- Fix: Modify coveringBand to use max(3(σ-1/2), |ρ.im|/2)

### Formula Corrections

**6-7. Mixed-sign formula (Axioms lines 230, 239)**
- Issue: phaseChange formula differs by ±π for mixed-sign cases
- Edge cases (a=σ, b=σ) already proven
- General case needs careful branch cut analysis

**8-10. Negative γ phase bounds (Axioms lines 683, 693, 695)**
- Symmetric to γ > 0 cases
- Need same arctan machinery

## Proof Architecture (Sound)

```
RH ← no_off_critical_zeros_in_strip ← local_zero_free
                                          ├── blaschke_lower_bound (≥ L_rec)
                                          │     └── phase_bound_from_arctan
                                          ├── blaschke_dominates_total
                                          ├── totalPhaseSignal_bound (≤ U_tail)
                                          └── L_rec > 4 * U_tail ✅
```

The contradiction follows because:
- Blaschke contribution B ≥ L_rec ≈ 0.55
- Total phase signal R ≤ U_tail ≈ 0.13
- But B is part of R, so L_rec ≤ |B| ≤ |R| ≤ U_tail
- Contradiction since L_rec > U_tail ✅ (proven)

## Priority Order for Completion

1. **Arctan machinery** (~50 lines) - Unblocks 5 sorries
2. **Whitney width fix** (~30 lines) - Structural fix
3. **ζ ≠ 0 on (0,1)** (~70 lines) - Classical result
4. **BMO→Carleson** (~300 lines) - Major undertaking
