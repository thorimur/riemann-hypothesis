import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateOfWhittaker
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nondegenerate_of_whittaker : PositivityTheory.PfSWUS.NDOfWhit := by
  first | exact @GlobalTheory.CompanionTheory.SWGlue.ndOfWhit | exact GlobalTheory.CompanionTheory.SWGlue.ndOfWhit | (intros; apply GlobalTheory.CompanionTheory.SWGlue.ndOfWhit <;> assumption)
