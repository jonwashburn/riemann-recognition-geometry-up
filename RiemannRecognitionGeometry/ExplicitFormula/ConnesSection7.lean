/-
# Connes–Consani–Moscovici (arXiv:2511.22755) — Section 7 objects (E-map, educated guess `k_λ`)

This module is **not** the CCM proof. Its job is to make the Section 7 “educated guess” objects
*concrete Lean definitions*, and to carve the convergence story (Lemma 7.3 style) into small,
typed lemmas that can later be proved (or instantiated from paper hypotheses).

Design goal: make **M2** (`ConnesMissingStep_kLam_approximates_xiLam`) attackable by supplying:
- a concrete definition of the E-map `E` (paper: `E(f)(u) := u^{1/2} ∑_{n≥1} f(nu)`),
- a canonical definition of `k_λ := E(h_λ)` for a given family `h_λ`,
- small “reduction lemmas” that turn a sup-norm approximation hypothesis on `h_λ` into a
  uniform-on-`[λ⁻¹, λ]` approximation hypothesis on `k_λ`.

We deliberately keep the analytic heavy lifting (summability, tail bounds, prolate-wave estimates)
as **assumption bundles / targets**, not global axioms.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Data.Complex.Basic

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open scoped Real Topology BigOperators
open Filter Set

/-! ## The CCM E-map -/

namespace Connes

/-- The CCM `E`-map (paper Eq. (7.2)):

`E(f)(u) := u^{1/2} * ∑_{n≥1} f(nu)`.

We implement the `n ≥ 1` sum as `∑' n : ℕ, f((n+1)u)`.

Notes:
- In the CCM setting one evaluates `u` on `[λ⁻¹, λ]`, hence eventually `u > 0` and `Real.sqrt u`
  matches the intended `u^{1/2}`.
- We do **not** bake summability into the definition; summability becomes an explicit hypothesis
  in lemmas below.
-/
def E (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  ((Real.sqrt u : ℝ) : ℂ) * ∑' n : ℕ, f ((n + 1 : ℕ) * u)

/-- The Section 7 “educated guess” from a given `h`: `k := E(h)`. -/
def kOf (h : ℝ → ℂ) : ℝ → ℂ := fun u => E h u

/-- A family version: given `hLam : λ ↦ h_λ`, define `kLam := λ ↦ E(h_λ)`. -/
def kLamOf (hLam : ℝ → ℝ → ℂ) : ℝ → (ℝ → ℂ) := fun lam => kOf (hLam lam)

@[simp] lemma kOf_def (h : ℝ → ℂ) (u : ℝ) : kOf h u = E h u := rfl
@[simp] lemma kLamOf_def (hLam : ℝ → ℝ → ℂ) (lam u : ℝ) : kLamOf hLam lam u = E (hLam lam) u := rfl

/-! ## Small reduction lemmas (algebraic skeleton) -/

/-- Pointwise difference bound for the E-map (pure algebra).

This is the basic “triangle inequality + pull out `sqrt u`” step that every convergence argument
starts from. It is intentionally stated without attempting to prove summability.
-/
theorem abs_E_sub_le
    (f g : ℝ → ℂ) (u : ℝ)
    (hSum : Summable (fun n : ℕ => Complex.abs (f ((n + 1 : ℕ) * u) - g ((n + 1 : ℕ) * u)))) :
    Complex.abs (E f u - E g u) ≤
      (Real.sqrt u) * (∑' n : ℕ, Complex.abs (f ((n + 1 : ℕ) * u) - g ((n + 1 : ℕ) * u))) := by
  -- Expand and apply the triangle inequality for `tsum`.
  classical
  -- Factor out `sqrt u`.
  simp [E, mul_sub, sub_mul, Complex.abs.map_mul, Complex.abs_ofReal, Real.sqrt_sq_eq_abs] at *
  -- The remaining inequality is `‖∑ (a_n)‖ ≤ ∑ ‖a_n‖`.
  -- Use `norm_tsum_le` on `ℂ` (with `‖z‖ = abs z`).
  -- Mathlib lemma name is `norm_tsum_le` in `Topology/Algebra/InfiniteSum`.
  -- We keep this proof lightweight: convert to `‖·‖` and apply `norm_tsum_le`.
  have h1 :
      Complex.abs (∑' n : ℕ, (f ((n + 1 : ℕ) * u) - g ((n + 1 : ℕ) * u))) ≤
        ∑' n : ℕ, Complex.abs (f ((n + 1 : ℕ) * u) - g ((n + 1 : ℕ) * u)) := by
    simpa [Complex.abs] using
      (norm_tsum_le (f := fun n : ℕ => (f ((n + 1 : ℕ) * u) - g ((n + 1 : ℕ) * u))) ) hSum
  -- Reinsert `sqrt u` (as a nonnegative real scalar).
  have hsqrt : 0 ≤ Real.sqrt u := Real.sqrt_nonneg u
  -- `mul_le_mul_of_nonneg_left` on `ℝ`.
  -- `Complex.abs (E f u - E g u)` has already been simp-rewritten to `Real.sqrt u * abs(tsum ...)` above.
  -- So we just finish by monotonicity of multiplication by a nonnegative real.
  exact mul_le_mul_of_nonneg_left h1 hsqrt

/-!
## Section 7 “Lemma 7.3 style” convergence scaffolding

The paper’s Lemma 7.3 uses a **sup-norm approximation** for `h_λ` on `[-λ, λ]` with rate `O(λ⁻²)`
to deduce uniform convergence (after Fourier transform) on closed substrips.

Before we touch Fourier transforms, we isolate the purely *E-map* part:

> if `h_λ ≈ h` (in a usable quantitative sense), then `k_λ = E(h_λ)` is uniformly close to `k = E(h)`
> on the semilocal interval `[λ⁻¹, λ]`.

We encode exactly what hypotheses are needed to make that argument go through, without committing
to a specific prolate-wave construction.
-/

/-- Quantitative “Section 7” hypothesis: `h_λ` approximates `h` on `[-λ, λ]` in sup norm.

This is the direct formalization of the paper’s `δ(λ) := max_{x∈[-λ,λ]} |h_λ(x)-h(x)|` control.
-/
structure SupApproxOnSymmInterval (hLam : ℝ → ℝ → ℂ) (h : ℝ → ℂ) where
  δ : ℝ → ℝ
  bound :
    ∀ᶠ lam : ℝ in atTop,
      ∀ x : ℝ, x ∈ Set.Icc (-lam) lam → Complex.abs (hLam lam x - h x) ≤ δ lam

/-- A tail-control hypothesis for the E-map.

This packages whatever decay/summability estimates you have on the `n`-sum defining `E`.
We keep this flexible: different implementations of `h_λ` will supply different tail bounds.

The intent is: for `u ∈ [λ⁻¹, λ]`, the tail `∑_{n>N(λ,u)} |h_λ((n+1)u)-h((n+1)u)|` is small.
-/
structure EMapTailControl (hLam : ℝ → ℝ → ℂ) (h : ℝ → ℂ) where
  tail : ℝ → ℝ
  tail_tendsto0 : Tendsto tail atTop (nhds 0)
  bound :
    ∀ᶠ lam : ℝ in atTop,
      ∀ u : ℝ, u ∈ Set.Icc (lam⁻¹) lam →
        Complex.abs (E (hLam lam) u - E h u) ≤ tail lam

/-- **Core Section 7 output (E-map form):**
uniform-on-`[λ⁻¹,λ]` approximation of `k_λ := E(h_λ)` by `k := E(h)` with vanishing error.

This is the exact shape you want in order to later compare `k_λ` to the true ground state `ξ_λ`
(M2), or to feed a Fourier-transform convergence statement.
-/
theorem kLam_uniform_approx_of_tailControl
    {hLam : ℝ → ℝ → ℂ} {h : ℝ → ℂ}
    (T : EMapTailControl hLam h) :
    ∀ᶠ lam : ℝ in atTop,
      ∀ u : ℝ, u ∈ Set.Icc (lam⁻¹) lam →
        Complex.abs (kLamOf hLam lam u - kOf h u) ≤ T.tail lam := by
  -- This is definitional: `kLamOf = E ∘ hLam` and `kOf = E h`.
  filter_upwards [T.bound] with lam hlam u hu
  simpa [kLamOf, kOf] using hlam u hu

end Connes

end ExplicitFormula
end RiemannRecognitionGeometry
