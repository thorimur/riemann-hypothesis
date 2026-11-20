import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSumHolds
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_sum_holds : ∀ D : D7, PerSum D := by
  first | exact @GlobalTheory.SeeSaw.perSum_all | exact GlobalTheory.SeeSaw.perSum_all | (intros; apply GlobalTheory.SeeSaw.perSum_all <;> assumption)
