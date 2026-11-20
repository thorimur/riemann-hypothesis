import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoreChainPreStepsExistOfDepthCongruence
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.core_chain_pre_steps_exist_of_depth_congruence : DepFixed → PreOK := by
  first | exact @GlobalTheory.CoreOnto.PreSteps.preOK | exact GlobalTheory.CoreOnto.PreSteps.preOK | (intros; apply GlobalTheory.CoreOnto.PreSteps.preOK <;> assumption)
