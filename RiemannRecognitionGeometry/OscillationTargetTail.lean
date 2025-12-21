/-
# B2′ interface: renormalized/local tail oscillation target (scaffolding)

This file introduces the Lean-facing interface corresponding to the paper’s **B2′**:
a localized oscillation/BMO certificate for a **renormalized tail** boundary datum.

At this stage we do *not* implement the renormalization itself. Instead we:
- define a placeholder boundary datum `tailLogAbs I ρ K : ℝ → ℝ`,
- define a localized BMO predicate (already in `FeffermanStein.lean`),
- package the paper-facing hypothesis as `OscillationTargetTail`,
- and record minimal axiom stubs needed to drive a renormalized contradiction.

This is purely structural: it keeps Lean aligned with the corrected written proof plan.
-/

import RiemannRecognitionGeometry.Assumptions
import RiemannRecognitionGeometry.FeffermanStein
import RiemannRecognitionGeometry.MuCarleson

noncomputable section

namespace RiemannRecognitionGeometry

open Real Complex
open scoped BigOperators

/-- A local zero “datum” used to build the renormalized tail potential.

In paper terms, a zero `ρ' = 1/2 + σ + iγ` contributes the logarithmic potential
\[
  \tfrac12 \log((t-γ)^2 + σ^2)
\]
with multiplicity. We package `(σ,γ,multiplicity)` as a single record.

This is **not** the arithmetic construction of the zero set; it is just a convenient carrier
for the finite multiset that B2′ subtracts. -/
structure LocalZeroDatum where
  /-- `σ = Re(ρ') - 1/2` (allowing `σ = 0` for critical-line zeros). -/
  sigma : ℝ
  /-- `γ = Im(ρ')`. -/
  gamma : ℝ
  /-- Multiplicity of the zero. -/
  mult : ℕ

/-- Opaque finite set of local zeros used by the renormalization window.

Paper meaning: the finite multiset `𝒵(I,ρ;K)` of zeros (with multiplicity) in the chosen
local window above the base interval `I`, excluding the distinguished off-line zero `ρ`.

We keep this opaque: constructing it from the actual zeta zeros is part of the core B2′ work. -/
opaque localZeroData (I : WhitneyInterval) (ρ : ℂ) (K : ℕ) : Finset LocalZeroDatum

/-- Opaque placeholder for the σ-weighted off-line zero measure μ. -/
opaque muOffCritical : MeasureTheory.Measure (ℝ × ℝ)

/-- **Spec (window membership):** every datum in `localZeroData I ρ K` lies in the B2′ local window.

This ties the opaque carrier `localZeroData` to the geometric cutoff used in the plan/paper (`inLocalWindow`).
It is intentionally one-way (“membership ⇒ window”), since the converse direction would require
constructing the actual zeta-zero multiset.
-/
axiom localZeroData_mem_window
    {I : WhitneyInterval} {ρ : ℂ} {K : ℕ} {z : LocalZeroDatum}
    (hz : z ∈ localZeroData I ρ K) :
    inLocalWindow I.len I.t0 K z.sigma z.gamma

/-- **Spec (multiplicity sanity):** any listed local datum has strictly positive multiplicity. -/
axiom localZeroData_mult_pos
    {I : WhitneyInterval} {ρ : ℂ} {K : ℕ} {z : LocalZeroDatum}
    (hz : z ∈ localZeroData I ρ K) :
    0 < z.mult

/-- **Spec (exclude the distinguished off-line zero):** the local renormalization data does not
include the distinguished zero `ρ` itself.

Since `LocalZeroDatum` only stores the half-plane coordinates `(σ,γ)`, this is stated as the
negation of matching both `σ = Re(ρ)-1/2` and `γ = Im(ρ)`. -/
axiom localZeroData_not_distinguished
    {I : WhitneyInterval} {ρ : ℂ} {K : ℕ} {z : LocalZeroDatum}
    (hz : z ∈ localZeroData I ρ K) :
    ¬ (z.gamma = ρ.im ∧ z.sigma = ρ.re - 1/2)

/-- The logarithmic potential of a single local zero datum. -/
def localZeroPotential (z : LocalZeroDatum) (t : ℝ) : ℝ :=
  ((z.mult : ℝ) / 2) * Real.log ((t - z.gamma) ^ 2 + z.sigma ^ 2)

/-- The total local potential `Φ_{I,ρ;K}` (finite sum over the local zero data). -/
def localPotential (I : WhitneyInterval) (ρ : ℂ) (K : ℕ) (t : ℝ) : ℝ :=
  (localZeroData I ρ K).sum fun z => localZeroPotential z t

/-- The σ-weighted mass of the local zero data (multiplicity-weighted).

This is the discrete analogue of the off-critical zero measure mass
\(\sum \sigma_\rho\) over the local window, where `σ = Re(ρ)-1/2`.
Critical-line zeros have `σ = 0` and hence contribute zero mass. -/
def localZeroSigmaMass (I : WhitneyInterval) (ρ : ℂ) (K : ℕ) : ℝ :=
  (localZeroData I ρ K).sum fun z => (z.mult : ℝ) * z.sigma

/-- Dilated Whitney interval used to represent the enlarged local window `Q_K(I)` as a Carleson box.

If `I = (t0,L)`, we set `I_dil = (t0, 2^(K+1)·L)`. Then `carlesonBox I_dil 2` has horizontal span
`|γ-t0| ≤ 2^(K+1)·L` and vertical height `σ ≤ 2^(K+3)·L`, matching `inLocalWindow`. -/
def dilatedWhitney (I : WhitneyInterval) (K : ℕ) : WhitneyInterval :=
  { t0 := I.t0
    len := (2 : ℝ)^(K+1) * I.len
    len_pos := by
      have hpow : 0 < (2 : ℝ)^(K+1) := by positivity
      exact mul_pos hpow I.len_pos }

lemma mem_carlesonBox_dilatedWhitney_two_implies_inLocalWindow
    {I : WhitneyInterval} {K : ℕ} {p : ℝ × ℝ}
    (hp : p ∈ carlesonBox (dilatedWhitney I K) 2) :
    inLocalWindow I.len I.t0 K p.2 p.1 := by
  rcases hp with ⟨hp_int, hpσ_pos, hpσ_le⟩
  -- unpack `p.1 ∈ (dilatedWhitney I K).interval` into the |γ-t0| bound
  have hγ : |p.1 - I.t0| ≤ (2 : ℝ)^(K+1) * I.len := by
    -- interval membership is equivalent to `t0 - len ≤ γ ≤ t0 + len`
    have hmem : p.1 ∈ Set.Icc (I.t0 - (2 : ℝ)^(K+1) * I.len) (I.t0 + (2 : ℝ)^(K+1) * I.len) := by
      simpa [WhitneyInterval.interval, dilatedWhitney, sub_eq_add_neg, add_assoc, add_left_comm,
        add_comm] using hp_int
    rcases hmem with ⟨hl, hr⟩
    -- convert to absolute value bound
    have : -((2 : ℝ)^(K+1) * I.len) ≤ p.1 - I.t0 ∧ p.1 - I.t0 ≤ (2 : ℝ)^(K+1) * I.len := by
      constructor <;> linarith
    exact abs_le.2 this
  -- vertical bound: `p.2 ≤ 2^(K+3) * I.len`
  have hσ : p.2 ≤ (2 : ℝ)^(K+3) * I.len := by
    -- in `carlesonBox` with aperture 2: σ ≤ 2 * (2 * len)
    -- for `dilatedWhitney`, `len = 2^(K+1) * I.len`, so RHS is `4 * 2^(K+1) * I.len = 2^(K+3) * I.len`.
    have : p.2 ≤ 2 * (2 * (dilatedWhitney I K).len) := by
      simpa [carlesonBox] using hpσ_le
    -- simplify the RHS
    have hR : 2 * (2 * (dilatedWhitney I K).len) = (2 : ℝ)^(K+3) * I.len := by
      -- `dilatedWhitney.len = 2^(K+1)·I.len`, and `2*(2*len) = 4*len = 2^2*len`.
      have hpow : (2 : ℝ)^(K+3) = (2 : ℝ)^(K+1) * (2 : ℝ)^2 := by
        -- `K+3 = (K+1)+2`
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using (pow_add (2 : ℝ) (K+1) 2)
      -- compute
      calc
        2 * (2 * (dilatedWhitney I K).len)
            = (2 : ℝ)^2 * (dilatedWhitney I K).len := by
                -- `(2^2) = 2*2`
                simp [pow_two, mul_assoc]
        _ = (2 : ℝ)^2 * ((2 : ℝ)^(K+1) * I.len) := by
                simp [dilatedWhitney, mul_assoc]
        _ = ((2 : ℝ)^(K+1) * (2 : ℝ)^2) * I.len := by
                ring
        _ = (2 : ℝ)^(K+3) * I.len := by
                simp [hpow, mul_assoc, mul_left_comm, mul_comm]
    simpa [hR] using this
  refine ⟨le_of_lt hpσ_pos, hσ, ?_⟩
  -- rewrite `|γ - t0|` in the same order as `hγ`
  simpa [abs_sub_comm, sub_eq_add_neg] using hγ

/-! ### Spec: relate μ and the local zero carrier (Route A bookkeeping)

To connect μ-Carleson packing statements to the finitary renormalization window `localZeroData`,
we record a minimal (axiomatized) bridge: the σ-weighted mass of `localZeroData` is controlled by
the μ-mass of the corresponding enlarged Carleson box.
-/

/-- **Spec (Route A bookkeeping):** the σ-mass of `localZeroData` is bounded by μ on the enlarged box.

This should be provable once `muOffCritical` is actually constructed as the σ-weighted off-line zero measure
and `localZeroData` is instantiated as the multiset of zeros in the local window. -/
axiom localZeroSigmaMass_le_muOffCritical
    (I : WhitneyInterval) (ρ : ℂ) (K : ℕ) :
    ENNReal.ofReal (localZeroSigmaMass I ρ K) ≤
      muOffCritical (carlesonBox (dilatedWhitney I K) 2)

/-- Renormalized tail boundary log-modulus datum associated to a Whitney interval `I`,
an off-line candidate zero `ρ`, and a cutoff parameter `K`.

Paper meaning: `t ↦ log|ζ(1/2+it)| - Φ_{I,ρ;K}(t)` where `Φ` is a finite sum of local zero-potentials.

This definition is now *definitional* in Lean, but it is still parameterized by an opaque
finite local zero set `localZeroData`. Proving its BMO smallness is exactly the B2′ work. -/
def tailLogAbs (I : WhitneyInterval) (ρ : ℂ) (K : ℕ) (t : ℝ) : ℝ :=
  logAbsXi t - localPotential I ρ K t

/-- **B2′ (Lean-facing)**: existence of a fixed cutoff `K` such that the renormalized tail datum has
localized BMO norm ≤ `C_tail` on every Whitney base interval (for every `ρ`).

This is the intended replacement for the deprecated global `OscillationTarget`. -/
def OscillationTargetTail : Prop :=
  ∃ K : ℕ, ∀ (ρ : ℂ) (I : WhitneyInterval),
    InBMOWithBoundOnWhitney (tailLogAbs I ρ K) I C_tail

/-! ## Route A bridge (scaffold)

To mirror the paper’s “μ-Carleson ⇒ B2′” reduction lemma, we include a minimal (axiomatized)
bridge from a Carleson packing hypothesis for an abstract measure `μ` to `OscillationTargetTail`.

The actual construction/identification of the arithmetic μ (from zeta zeros) and the proof of
this implication is the RH-level core of Route A.
-/

/-!
**Note:** the Route‑A bridge is now implemented (as a *composed scaffold*) in
`RiemannRecognitionGeometry/MuCarlesonToTailDecay.lean`:

`MuCarleson` ⇒ (annulus-majorant stub) ⇒ `TailMeanOscDecay` ⇒ choose `K` ⇒ `OscillationTargetTail`.

The remaining axioms should live at the *sublemma* level (single-zero influence, annulus decay,
μ‑Carleson summation), not as one monolithic “μ‑Carleson ⇒ B2′” axiom.
-/

/-- Renormalized (cofactor) phase signal across a Whitney interval, expressed as a real number
via the `Real.Angle` norm.

For now we reuse the existing `rgCofactorPhaseAngle` as the phase channel, because it is already
the “cofactor phase” object exposed by `ClassicalAnalysisAssumptions.cofactor_green_identity_axiom_statement`.
The long-term plan is to make this phase correspond to the actual renormalized cofactor
`𝒢_{I,ρ;K}` in the paper. -/
def tailPhaseSignal (I : WhitneyInterval) (ρ : ℂ) (_K : ℕ) : ℝ :=
  ‖rgCofactorPhaseAngle ρ (I.t0 + I.len) - rgCofactorPhaseAngle ρ (I.t0 - I.len)‖

/-!
## Minimal driver stubs (to be proved later)

These two statements are the driver-facing pieces labeled (D1)/(D2) in the planning document.
They are currently axiomatized so the *structure* of the renormalized contradiction can be
implemented in Lean while the deep analytic number theory is developed.
-/

/-- **(D1) Upper bound stub.** Local BMO control of the tail datum implies a tail/cofactor phase bound. -/
axiom tailPhaseSignal_bound
    (hCA : ClassicalAnalysisAssumptions)
    {I : WhitneyInterval} {ρ : ℂ} {K : ℕ}
    (hBMO : InBMOWithBoundOnWhitney (tailLogAbs I ρ K) I C_tail) :
    tailPhaseSignal I ρ K ≤ U_tail C_tail

/-- **(D2) Lower bound stub (centered Blaschke trigger).**

For an off-line zero `ρ`, let `I0` be the centered Whitney interval with half-length `2*(ρ.re-1/2)`.
Then the tail/cofactor phase signal across `I0` satisfies a **dominance** lower bound of the form
`L_rec - U_tail(C_tail) ≤ …`, uniformly in `K`.

This is the renormalized analog of the Blaschke trigger lower bound used in the existing driver. -/
axiom tailPhaseSignal_lower_bound_centered
    (ρ : ℂ) (hρ_zero : completedRiemannZeta ρ = 0) (hρ_re : 1/2 < ρ.re) :
    let d : ℝ := ρ.re - 1/2
    let I0 : WhitneyInterval :=
      { t0 := ρ.im
        len := 2 * d
        len_pos := by
          have : 0 < d := by simp [d]; linarith
          nlinarith }
    ∀ K : ℕ, L_rec - U_tail C_tail ≤ tailPhaseSignal I0 ρ K

end RiemannRecognitionGeometry
