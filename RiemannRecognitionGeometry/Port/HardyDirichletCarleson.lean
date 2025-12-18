/-
# Port scaffold: HardyDirichlet/Carleson → Recognition Geometry energy budget

This file is a **translation stub** between:

- this repo’s Recognition Geometry interfaces (`RiemannRecognitionGeometry/Assumptions.lean`), and
- the (disabled) blueprint file in the local `reality` repo:
  `/Users/jonathanwashburn/Projects/reality/IndisputableMonolith/RH/HardyDirichlet/Carleson.lean.disabled`.

We do **not** depend on the `reality/` repo as a Lake dependency (it is on a different Lean/Mathlib),
so we mirror the relevant *statement-shapes* here.

The purpose is to give us a faithful target interface that can later be proved from:

- Fefferman–Stein BMO→Carleson (classical),
- VK/zero-density packing (RH-specific), or
- a specialized “certificate field” argument for `U = Re log 𝒥`.
-/

import RiemannRecognitionGeometry.Assumptions
import RiemannRecognitionGeometry.Port.CofactorEnergy

noncomputable section

namespace RiemannRecognitionGeometry
namespace Port

/-!
## A faithful budget interface (what the blueprint is trying to provide)

In the Hardy/Dirichlet blueprint, one wants an estimate of the form

`Energy_Q(I)(U) ≤ K · |I|`

for a harmonic field `U` (typically `U = Re log 𝒥`) over Carleson/Whitney tents.

In the RG development, the downstream consumer only needs an **energy constant**
`E ≤ K_tail(M)` per Whitney interval (see `RGAssumptions.j_carleson_energy_axiom_statement`).

To avoid baking in a particular analytic definition of “energy” at this stage, we parameterize
by an abstract functional `Ebox : ℂ → WhitneyInterval → ℝ` intended to denote the relevant
Carleson-box energy of the RG cofactor field associated to a putative zero `ρ`.
-/

/-- A Hardy/Dirichlet-style Carleson energy budget for the RG cofactor field.

`Ebox ρ I` should be read as the **raw box energy** over `I` (so it scales like `|I|`).

This is the interface we ultimately want to *prove* (or at least justify) in `riemann-geometry-rs`
using classical analysis, matching the blueprint’s intent. -/
structure HardyDirichletCarlesonBudget (Ebox : ℂ → WhitneyInterval → ℝ) : Prop where
  /-- Nonnegativity of the energy functional (sanity). -/
  Ebox_nonneg : ∀ ρ I, 0 ≤ Ebox ρ I

  /-- **Budget bound**: for a zero `ρ` captured by interval `I`, the cofactor box energy is controlled
  by the scale-correct quantity `K_tail M · |I|` (here `|I| = 2*I.len`). -/
  cofactor_boxEnergy_le :
    ∀ (I : WhitneyInterval) (ρ : ℂ) (M : ℝ),
      InBMOWithBound (cofactorLogAbs ρ) M →
      completedRiemannZeta ρ = 0 →
      ρ.im ∈ I.interval →
      Ebox ρ I ≤ K_tail M * (2 * I.len)

/-!
## Relationship to the current RG assumption surface

Today, the RG main chain carries an `RGAssumptions` bundle whose key field is
`j_carleson_energy_axiom_statement`.

That field is *intended* to be discharged from an estimate like `cofactor_boxEnergy_le` above,
but the current `RGAssumptions` field does not record the energy inequality itself (only the
existence of an energy constant).

So at the moment we only provide a **documentation lemma** that explains the intended reduction.
When we refactor the RG assumption surface to be faithful (or introduce a V2 surface), this file
is the bridge point.
-/

end Port
end RiemannRecognitionGeometry
