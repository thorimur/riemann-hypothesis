import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.MultiplicityOneUnitaryBranchingOfGapHyp
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.DoubleCosetBesselBoundOfGapConstantLe

namespace GlobalTheory

theorem uniqGap_and_besselOfW : GlobalTheory.GapIn.UniqGap ∧ Formalism.L2.SG.LocWSOf.BesselOfW :=
  ⟨CompanionTheory.Lime.BM.uniqGap_holds, Formalism.MainNotions.BridgeCS3dBOW.besselOfW_holds⟩

end GlobalTheory
