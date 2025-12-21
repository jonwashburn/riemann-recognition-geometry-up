/-
# Route 3′: Hurwitz / locally-uniform convergence gate (Connes-style approximants)

Several operator-theoretic approaches (e.g. Connes–Consani–Moscovici `arXiv:2511.22755`)
produce a sequence of entire functions (often via regularized determinants / Fourier transforms)
whose zeros lie **exactly on the real axis** in the *spectral parameter* (the variable in which
Riemann’s `Ξ` is written as `Ξ(t) = ξ(1/2 + i t)`). If one can then prove **locally uniform
convergence** of these approximants to the completed target `Ξ`, a classical Hurwitz-type
argument implies the limit is also zero-free off the real axis (inside the critical strip).

Mathlib currently has strong infrastructure for locally uniform limits of holomorphic functions
(`Mathlib.Analysis.Complex.LocallyUniformLimit`) but does not expose a ready-to-use Hurwitz
theorem about **preservation of nonvanishing**. We therefore isolate that analytic fact as a
single named axiom/target, so the Connes Route 3′ pipeline can be expressed cleanly in Lean.
-/

import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Topology

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open Set Filter
open scoped Real Topology

/-! ## The critical strip in the `t`-variable (`Ξ(t) = ξ(1/2 + i t)`) -/

/-- The open horizontal strip `|Im(t)| < 1/2`. This corresponds to `0 < Re(s) < 1` under `s = 1/2 + i t`. -/
def strip : Set ℂ := {t : ℂ | abs t.im < (1 / 2 : ℝ)}

/-- Upper half of the strip: `0 < Im(t) < 1/2`. -/
def upperStrip : Set ℂ := {t : ℂ | 0 < t.im ∧ t.im < (1 / 2 : ℝ)}

/-- Lower half of the strip: `-1/2 < Im(t) < 0`. -/
def lowerStrip : Set ℂ := {t : ℂ | (- (1 / 2 : ℝ)) < t.im ∧ t.im < 0}

lemma upperStrip_subset_strip : upperStrip ⊆ strip := by
  intro t ht
  have h0 : 0 < t.im := ht.1
  have hhalf : t.im < (1 / 2 : ℝ) := ht.2
  have habs : abs t.im < (1 / 2 : ℝ) := by
    -- since `0 < im`, `abs im = im`
    simpa [abs_of_pos h0] using hhalf
  exact habs

lemma lowerStrip_subset_strip : lowerStrip ⊆ strip := by
  intro t ht
  have hneg : t.im < 0 := ht.2
  have hgt : (- (1 / 2 : ℝ)) < t.im := ht.1
  have habs : abs t.im < (1 / 2 : ℝ) := by
    -- since `im < 0`, `abs im = -im`
    have : -t.im < (1 / 2 : ℝ) := by
      -- from `-1/2 < im` we get `-im < 1/2`
      linarith
    simpa [abs_of_neg hneg] using this
  exact habs

lemma isOpen_strip : IsOpen strip := by
  -- `t ↦ |Im(t)|` is continuous, so `{ |Im(t)| < 1/2 }` is open.
  simpa [strip] using isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

lemma isOpen_upperStrip : IsOpen upperStrip := by
  -- intersection of two open halfspaces for `im`
  have h1 : IsOpen {t : ℂ | 0 < t.im} := isOpen_lt continuous_const Complex.continuous_im
  have h2 : IsOpen {t : ℂ | t.im < (1 / 2 : ℝ)} := isOpen_lt Complex.continuous_im continuous_const
  simpa [upperStrip, Set.setOf_and] using h1.inter h2

lemma isOpen_lowerStrip : IsOpen lowerStrip := by
  have h1 : IsOpen {t : ℂ | (- (1 / 2 : ℝ)) < t.im} := isOpen_lt continuous_const Complex.continuous_im
  have h2 : IsOpen {t : ℂ | t.im < 0} := isOpen_lt Complex.continuous_im continuous_const
  simpa [lowerStrip, Set.setOf_and] using h1.inter h2

private lemma isLinearMap_im : IsLinearMap ℝ (fun z : ℂ => z.im) := by
  refine ⟨?_, ?_⟩
  · intro x y; simp
  · intro a x; simp

lemma isPreconnected_strip : IsPreconnected strip := by
  -- strip is convex (intersection of two halfspaces), hence preconnected
  have h1 : Convex ℝ {t : ℂ | (- (1 / 2 : ℝ)) < t.im} :=
    convex_halfSpace_gt (𝕜 := ℝ) (E := ℂ) (β := ℝ) (f := fun z : ℂ => z.im) isLinearMap_im (- (1 / 2 : ℝ))
  have h2 : Convex ℝ {t : ℂ | t.im < (1 / 2 : ℝ)} :=
    convex_halfSpace_lt (𝕜 := ℝ) (E := ℂ) (β := ℝ) (f := fun z : ℂ => z.im) isLinearMap_im (1 / 2 : ℝ)
  have hconv : Convex ℝ strip := by
    -- `|im| < 1/2` is equivalent to `-1/2 < im ∧ im < 1/2`
    have : strip = ({t : ℂ | (- (1 / 2 : ℝ)) < t.im} ∩ {t : ℂ | t.im < (1 / 2 : ℝ)}) := by
      ext t
      constructor
      · intro ht
        have ht' : abs t.im < (1 / 2 : ℝ) := by
          simpa [strip] using ht
        exact (abs_lt.mp ht')
      · rintro ⟨hgt, hlt⟩
        have hgt' : (- (1 / 2 : ℝ)) < t.im := by simpa using hgt
        have hlt' : t.im < (1 / 2 : ℝ) := by simpa using hlt
        exact abs_lt.mpr ⟨hgt', hlt'⟩
    -- rewrite and use convexity of intersection
    rw [this]
    exact h1.inter h2
  exact hconv.isPreconnected

lemma isPreconnected_upperStrip : IsPreconnected upperStrip := by
  have h1 : Convex ℝ {t : ℂ | 0 < t.im} :=
    convex_halfSpace_gt (𝕜 := ℝ) (E := ℂ) (β := ℝ) (f := fun z : ℂ => z.im) isLinearMap_im 0
  have h2 : Convex ℝ {t : ℂ | t.im < (1 / 2 : ℝ)} :=
    convex_halfSpace_lt (𝕜 := ℝ) (E := ℂ) (β := ℝ) (f := fun z : ℂ => z.im) isLinearMap_im (1 / 2 : ℝ)
  have : upperStrip = ({t : ℂ | 0 < t.im} ∩ {t : ℂ | t.im < (1 / 2 : ℝ)}) := by
    ext t; simp [upperStrip, and_left_comm, and_assoc, and_comm, Set.setOf_and]
  rw [this]
  exact (h1.inter h2).isPreconnected

lemma isPreconnected_lowerStrip : IsPreconnected lowerStrip := by
  have h1 : Convex ℝ {t : ℂ | (- (1 / 2 : ℝ)) < t.im} :=
    convex_halfSpace_gt (𝕜 := ℝ) (E := ℂ) (β := ℝ) (f := fun z : ℂ => z.im) isLinearMap_im (- (1 / 2 : ℝ))
  have h2 : Convex ℝ {t : ℂ | t.im < 0} :=
    convex_halfSpace_lt (𝕜 := ℝ) (E := ℂ) (β := ℝ) (f := fun z : ℂ => z.im) isLinearMap_im 0
  have : lowerStrip = ({t : ℂ | (- (1 / 2 : ℝ)) < t.im} ∩ {t : ℂ | t.im < 0}) := by
    ext t; simp [lowerStrip, and_left_comm, and_assoc, and_comm, Set.setOf_and]
  rw [this]
  exact (h1.inter h2).isPreconnected

/-! ## Zero-free predicates -/

/-- A function is zero-free on a set `U`. -/
def ZeroFreeOn (f : ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∀ z ∈ U, f z ≠ 0

/--
A function is zero-free off the real axis **inside the critical strip** (`|Im(t)| < 1/2`),
packaged as zero-freeness on the upper and lower halves of the strip.
-/
def ZeroFreeOffRealAxisInStrip (f : ℂ → ℂ) : Prop :=
  ZeroFreeOn f upperStrip ∧ ZeroFreeOn f lowerStrip

/-! ## Hurwitz-style nonvanishing preservation (target axiom) -/

/--
**Hurwitz nonvanishing principle (target axiom).**

If `Fₙ` are holomorphic on an open, preconnected set `U`, converge locally uniformly to `f` on `U`,
and each `Fₙ` is zero-free on `U`, then either `f` is identically `0` on `U` or `f` is zero-free on `U`.

We expose the useful “nontrivial ⇒ zero-free” direction as a single named axiom, since Mathlib does
not currently provide it as a lemma.
-/
axiom hurwitz_zeroFree_of_tendstoLocallyUniformlyOn
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (hUopen : IsOpen U) (hUconn : IsPreconnected U)
    (hF : ∀ n : ℕ, DifferentiableOn ℂ (F n) U)
    (hLim : TendstoLocallyUniformlyOn F f atTop U)
    (hZeroFree : ∀ n : ℕ, ZeroFreeOn (F n) U)
    (hNontriv : ∃ z ∈ U, f z ≠ 0) :
    ZeroFreeOn f U

/-! ## A packaged Hurwitz gate for “zeros are real (in the strip)” -/

/--
Route 3′ Hurwitz gate (Connes-style):

If we have approximants `F n` that are holomorphic and zero-free on the upper/lower parts
of the strip `|Im(t)| < 1/2`, and they converge locally uniformly to `f` on that strip, then `f`
is also zero-free off the real axis in that strip.

This is the exact “final analytic step” needed for the Connes-style determinant-approximation
strategy once locally uniform convergence is established.
-/
structure HurwitzOffRealAxisInStripGate (f : ℂ → ℂ) where
  F : ℕ → ℂ → ℂ
  holo_upper  : ∀ n, DifferentiableOn ℂ (F n) upperStrip
  holo_lower  : ∀ n, DifferentiableOn ℂ (F n) lowerStrip
  tendsto_strip : TendstoLocallyUniformlyOn F f atTop strip
  zeroFree_upper  : ∀ n, ZeroFreeOn (F n) upperStrip
  zeroFree_lower  : ∀ n, ZeroFreeOn (F n) lowerStrip
  nontriv_upper  : ∃ z ∈ upperStrip, f z ≠ 0
  nontriv_lower  : ∃ z ∈ lowerStrip, f z ≠ 0

namespace HurwitzOffRealAxisInStripGate

variable {f : ℂ → ℂ}

theorem zeroFree_upper_of_gate (H : HurwitzOffRealAxisInStripGate f) : ZeroFreeOn f upperStrip := by
  have hLimU : TendstoLocallyUniformlyOn (F H) f atTop upperStrip :=
    (tendsto_strip H).mono upperStrip_subset_strip
  exact hurwitz_zeroFree_of_tendstoLocallyUniformlyOn
    (hUopen := isOpen_upperStrip)
    (hUconn := isPreconnected_upperStrip)
    (hF := holo_upper H)
    (hLim := hLimU)
    (hZeroFree := zeroFree_upper H)
    (hNontriv := nontriv_upper H)

theorem zeroFree_lower_of_gate (H : HurwitzOffRealAxisInStripGate f) : ZeroFreeOn f lowerStrip := by
  have hLimU : TendstoLocallyUniformlyOn (F H) f atTop lowerStrip :=
    (tendsto_strip H).mono lowerStrip_subset_strip
  exact hurwitz_zeroFree_of_tendstoLocallyUniformlyOn
    (hUopen := isOpen_lowerStrip)
    (hUconn := isPreconnected_lowerStrip)
    (hF := holo_lower H)
    (hLim := hLimU)
    (hZeroFree := zeroFree_lower H)
    (hNontriv := nontriv_lower H)

theorem zeroFree_offRealAxisInStrip (H : HurwitzOffRealAxisInStripGate f) : ZeroFreeOffRealAxisInStrip f :=
  ⟨zeroFree_upper_of_gate H, zeroFree_lower_of_gate H⟩

end HurwitzOffRealAxisInStripGate

end ExplicitFormula
end RiemannRecognitionGeometry
