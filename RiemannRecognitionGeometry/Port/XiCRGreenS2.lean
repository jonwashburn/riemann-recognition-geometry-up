import RiemannRecognitionGeometry.Port.XiCRGreenS2Interfaces

noncomputable section

namespace RiemannRecognitionGeometry
namespace Port

namespace XiCRGreenS2

/-- `S2` (faithful form, xi-side): there exists a lift-based Green trace identity plus its pairing bound. -/
def Assumptions : Prop :=
  ∃ T : XiCRGreenS2Interfaces.GreenTraceIdentity,
    XiCRGreenS2Interfaces.PairingBound T

/-- `S2a` + `S2b` ⇒ the strong xi CR/Green bound. -/
theorem xiCRGreenAssumptionsStrong_of_S2 (h : Assumptions) :
    XiCRGreenAssumptionsStrong := by
  rcases h with ⟨T, hB⟩
  exact XiCRGreenS2Interfaces.xiCRGreenAssumptionsStrong_of_greenTrace_and_pairing T hB

/-- `S2` also discharges the weaker xi CR/Green API by composing `S2 → Strong → Weak`. -/
theorem xiCRGreenAssumptions_of_S2 (h : Assumptions) :
    XiCRGreenAssumptions :=
  xiCRGreenAssumptions_of_xiCRGreenAssumptionsStrong
    (xiCRGreenAssumptionsStrong_of_S2 h)

end XiCRGreenS2

end Port
end RiemannRecognitionGeometry
