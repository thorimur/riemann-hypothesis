import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_zero_holds : PositivityTheory.PfSWUS.FourierZero := by
  first | exact @GlobalTheory.CompanionTheory.FourierN.fourierZero | exact GlobalTheory.CompanionTheory.FourierN.fourierZero | (intros; apply GlobalTheory.CompanionTheory.FourierN.fourierZero <;> assumption)
