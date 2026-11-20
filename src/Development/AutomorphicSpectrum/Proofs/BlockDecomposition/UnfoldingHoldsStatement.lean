import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingHolds
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolding_holds : PositivityTheory.PfSWUS.Unfold := by
  first | exact @GlobalTheory.CompanionTheory.SwUnf.unfold | exact GlobalTheory.CompanionTheory.SwUnf.unfold | (intros; apply GlobalTheory.CompanionTheory.SwUnf.unfold <;> assumption)
