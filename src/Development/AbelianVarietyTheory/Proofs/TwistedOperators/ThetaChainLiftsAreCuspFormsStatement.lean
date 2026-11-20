import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainLiftsAreCuspForms
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChainLifts_areCuspForms : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, GlobalTheory.Chain.LiftCusp D := by
  first | exact @GlobalTheory.LiftCuspObj.liftCusp | exact GlobalTheory.LiftCuspObj.liftCusp | (intros; apply GlobalTheory.LiftCuspObj.liftCusp <;> assumption)
