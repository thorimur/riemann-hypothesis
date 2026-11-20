import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnisotropyOfRange
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.anisotropy_of_range : PositivityTheory.PfSWUS.AnisoOfRange := by
  first | exact @GlobalTheory.CompanionTheory.AnisoRange.anisoOfRange | exact GlobalTheory.CompanionTheory.AnisoRange.anisoOfRange | (intros; apply GlobalTheory.CompanionTheory.AnisoRange.anisoOfRange <;> assumption)
