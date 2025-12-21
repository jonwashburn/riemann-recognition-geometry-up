/-
# Real-zeros glue for Route 3′ (Connes-style approximants)

Several operator-theoretic constructions (e.g. Connes–van Suijlekom `arXiv:2511.23257`) produce
entire functions whose zeros are **all real** (in the `Ξ(t)` spectral variable).

Our Hurwitz gate (`ExplicitFormula/HurwitzGate.lean`) is phrased as *zero-freeness* on the
upper/lower halves of the strip `|Im(t)| < 1/2`. This file provides the tiny “glue lemma”:

`AllZerosReal f  →  ZeroFreeOn f upperStrip` and similarly for `lowerStrip`.
-/

import RiemannRecognitionGeometry.ExplicitFormula.HurwitzGate

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open Complex Set

/-- All zeros of `f` are real, i.e. `f z = 0` implies `Im(z)=0`. -/
def AllZerosReal (f : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, f z = 0 → z.im = 0

lemma zeroFreeOn_upperStrip_of_allZerosReal {f : ℂ → ℂ} (h : AllZerosReal f) :
    ZeroFreeOn f upperStrip := by
  intro z hz
  intro hf0
  have hiz : z.im = 0 := h z hf0
  have hzpos : 0 < z.im := hz.1
  linarith

lemma zeroFreeOn_lowerStrip_of_allZerosReal {f : ℂ → ℂ} (h : AllZerosReal f) :
    ZeroFreeOn f lowerStrip := by
  intro z hz
  intro hf0
  have hiz : z.im = 0 := h z hf0
  have hzneg : z.im < 0 := hz.2
  linarith

lemma zeroFreeOffRealAxisInStrip_of_allZerosReal {f : ℂ → ℂ} (h : AllZerosReal f) :
    ZeroFreeOffRealAxisInStrip f :=
  ⟨zeroFreeOn_upperStrip_of_allZerosReal h, zeroFreeOn_lowerStrip_of_allZerosReal h⟩

end ExplicitFormula
end RiemannRecognitionGeometry
