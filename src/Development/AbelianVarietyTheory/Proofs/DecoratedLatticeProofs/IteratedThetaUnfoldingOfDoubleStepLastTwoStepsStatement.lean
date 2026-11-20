import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedThetaUnfoldingOfDoubleStepLastTwoSteps
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedThetaUnfolding_of_doubleStep_lastTwoSteps : ∀ D : D7, DoubleStep D → LastLaw D → IT D := by
  first | exact @GlobalTheory.Unf.iter_of_doubleStep_lastLaw | exact GlobalTheory.Unf.iter_of_doubleStep_lastLaw | (intros; apply GlobalTheory.Unf.iter_of_doubleStep_lastLaw <;> assumption)
