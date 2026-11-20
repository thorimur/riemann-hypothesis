import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftPeriodRankZeroFubiniCompactQuotient
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleLiftPeriod_rankZero_fubini_compactQuotient : ∀ D : D7, LastLaw D := by
  first | exact @GlobalTheory.Unf.LastSteps.lastLaw | exact GlobalTheory.Unf.LastSteps.lastLaw | (intros; apply GlobalTheory.Unf.LastSteps.lastLaw <;> assumption)
