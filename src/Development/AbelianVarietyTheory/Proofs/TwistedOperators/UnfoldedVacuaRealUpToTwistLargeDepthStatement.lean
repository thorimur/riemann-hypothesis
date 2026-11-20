import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedVacuaRealUpToTwistLargeDepth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolded_vacua_real_up_to_twist_large_depth : Big fun ch => VacAt ch := by
  first | exact @GlobalTheory.RowVal.OneVac.big_vacAt | exact GlobalTheory.RowVal.OneVac.big_vacAt | (intros; apply GlobalTheory.RowVal.OneVac.big_vacAt <;> assumption)
