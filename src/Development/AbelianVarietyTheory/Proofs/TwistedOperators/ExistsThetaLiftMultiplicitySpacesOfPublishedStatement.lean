import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLiftMultiplicitySpacesOfHyp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaLift_multiplicitySpaces_of_hypotheses : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ D : D7, GlobalTheory.Chain.IoPair D := by
  first | exact @GlobalTheory.Chain.IoLift.ioPair_onObjects | exact GlobalTheory.Chain.IoLift.ioPair_onObjects | (intros; apply GlobalTheory.Chain.IoLift.ioPair_onObjects <;> assumption)
