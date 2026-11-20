import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoreChainLiftsSurjectiveOfEvenRank
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coreChain_lifts_surjective_of_evenRank : (∀ D : D7, GlobalTheory.EvenOnto.OntoAll D) → ComOK → StageOK → ChainEx → TopCols → CoreOnto := by
  first | exact @GlobalTheory.CoreOnto.coreOnto_of_chain | exact GlobalTheory.CoreOnto.coreOnto_of_chain | (intros; apply GlobalTheory.CoreOnto.coreOnto_of_chain <;> assumption)
