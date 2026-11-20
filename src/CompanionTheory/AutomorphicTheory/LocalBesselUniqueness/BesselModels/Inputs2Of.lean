import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.AtFormAdmOneOfSteps
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.Inputs

namespace CompanionTheory.Lime.BM

def Inputs2 : Prop := Formalism.FourierDecayAlt.ThreeDimData.DecLow ∧ Formalism.FourierDecayAlt.ThreeDimData.DecInf ∧ PI.KFinSmooth ∧ UniqGap

theorem inputs2_of (h : UniqGap) : Inputs2 := ⟨inputs.1, inputs.2.1, inputs.2.2.1, h⟩

end CompanionTheory.Lime.BM
