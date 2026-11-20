import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerMaximalCompactGeneral
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_maximal_compact_general : PositivityTheory.PfSWUS.WhitKAOfGenLt := by
  first | exact @GlobalTheory.CompanionTheory.IwaAd.whitKAOfGenLt | exact GlobalTheory.CompanionTheory.IwaAd.whitKAOfGenLt | (intros; apply GlobalTheory.CompanionTheory.IwaAd.whitKAOfGenLt <;> assumption)
