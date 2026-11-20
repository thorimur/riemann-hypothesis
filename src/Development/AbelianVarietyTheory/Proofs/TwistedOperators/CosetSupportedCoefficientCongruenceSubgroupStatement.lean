import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetSupportedCoefficientCongruenceSubgroup
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosetSupported_coefficient_congruenceSubgroup : CosSupp := by
  first | exact @GlobalTheory.CosSupport.cosSupp | exact GlobalTheory.CosSupport.cosSupp | (intros; apply GlobalTheory.CosSupport.cosSupp <;> assumption)
