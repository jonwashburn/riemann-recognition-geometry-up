# Sorry Transfer Map: Existing Solutions in Other Riemann Repos

## Executive Summary

Your other riemann repos have **significant completed work** that can be transferred:

| Repo | Total .lean files | Files with sorries in key dirs | Completeness |
|------|-------------------|-------------------------------|--------------|
| `riemann-finish/rh/` | ~100+ | **3 files, 18 sorries** | **MOST COMPLETE** |
| `riemann-side/BWP/` | 40 | ~15 files with sorries | Substantial work |
| `riemann-main` | 481 | Various | Good library |

**Key Finding**: `riemann-finish` has an almost-complete proof with only 18 sorries!

---

## riemann-finish (MOST COMPLETE)

**Location**: `/Users/jonathanwashburn/Projects/riemann-finish/riemann-extra/riemann/no-zeros/rh/`

### Proof Structure
- `Proof/Main.lean` - **0 sorries** - Main RH theorem assembly
- `Proof/Active.lean` - **0 sorries** - Active track proof

### Only 18 sorries total:
1. `RS/sealed/PoissonPlateauNew.lean` - 16 sorries (Poisson plateau construction)
2. `academic_framework/PoissonCayley.lean` - 1 sorry (Cayley transport)
3. `RS/DirectWedgeProof.lean` - 1 sorry (Wedge proof step)

### Key Completed Modules (0 sorries):
- `RS/SchurGlobalization.lean` - Schur function globalization
- `RS/OffZerosBridge.lean` - Off-zeros bridge
- `RS/XiExtBridge.lean` - Xi extension bridge
- `RS/Cayley.lean` - Cayley transform
- `RS/PinchCertificate.lean` - Pinch certificate
- `academic_framework/CompletedXi.lean` - Completed xi function
- `academic_framework/EulerProductMathlib.lean` - Euler product

---

## riemann-side (BOUNDARY WEDGE PROOF)

**Location**: `/Users/jonathanwashburn/Projects/riemann-side/Riemann/Riemann/RS/BWP/`

### Completed Modules (0 sorries):
- `PhaseVelocityProven.lean` - **Proven phase velocity hypothesis**
- `ZeroDensity.lean`
- `WindowClass.lean`
- `WedgeVerify.lean`
- `WedgeHypotheses.lean`
- `VKToCarlesonHypothesis.lean`
- `VKAnnularCountsReal.lean`
- `TailCarleson.lean`
- `ResidueHypothesis.lean`
- `PoissonExtension.lean`
- `PoissonExplicit.lean`
- `LogDerivativeDecomposition.lean`
- `KxiFinite.lean`
- `Laplacian.lean`
- `GreenIdentity.lean`
- `FeffermanStein.lean`
- `Definitions.lean`
- `Constants.lean`
- `CRGreenReal.lean`
- `CRGreenHypothesis.lean`
- `CRGreenConstantVerify.lean`
- `CRCalculus.lean`
- `CarlesonHypothesis.lean`
- `BandGeometry.lean`

### Key Partial Modules:
- `PhaseVelocityProof.lean` - 5 sorries
- `RHFromAxiomsAndPerZero.lean` - 3 sorries
- `RecognitionGeometry.lean` - 1 sorry

---

## riemann-main (LIBRARY)

**Location**: `/Users/jonathanwashburn/Projects/riemann-main/`

### Useful Completed Lemmas:

#### Mellin/Fourier:
- `PrimeNumberTheoremAnd/MellinCalculus.lean` - Mellin calculus utilities
- `PrimeNumberTheoremAnd/PerronFormula.lean` - Rectangle→Vertical integral lemmas
- `PrimeNumberTheoremAnd/Wiener.lean` - Fourier/Wiener lemmas

#### Explicit Formula:
- `Weil/ExplicitFormula_new.lean` - Weil explicit formula
- `Weil/ExplicitFormula.lean` - Original version

#### Det2/Euler Product:
- `academic_framework/DiagonalFredholm/Determinant.lean` - det₂ construction
- `RS/Det2Outer.lean` - det₂ outer construction

#### Zeta Bounds:
- `PrimeNumberTheoremAnd/ZetaBounds.lean` - Zeta function bounds

---

## Transfer Strategy

### Immediate Wins (copy/adapt):
1. **From riemann-finish**: The entire `Proof/` directory structure
2. **From riemann-finish**: `RS/SchurGlobalization.lean`, `RS/OffZerosBridge.lean`
3. **From riemann-side**: `PhaseVelocityProven.lean` approach

### Medium Effort:
1. **From riemann-main**: `MellinCalculus.lean` lemmas for Fourier inversion
2. **From riemann-main**: `PerronFormula.lean` for contour limits

### The 18 Remaining Sorries in riemann-finish:
These are the **actual blockers** for an unconditional proof:
1. Poisson plateau construction (16 sorries)
2. Cayley transport identity (1 sorry)
3. Direct wedge proof step (1 sorry)

---

## Recommendation

**Consider using riemann-finish as the primary proof repo** rather than riemann-geometry-rs.

riemann-finish is:
- More complete (18 sorries vs potentially more)
- Has clear proof structure
- Has most infrastructure already in place

The Route 3 approach in riemann-geometry-rs may be duplicating work that's already further along in riemann-finish.

