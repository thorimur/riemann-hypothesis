import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryChamberDecomposition
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_chamber_decomposition : PositivityTheory.SphericalProduct.ChamberU := by
  first | exact @GlobalTheory.CompanionTheory.ChamberInd.chamberU | exact GlobalTheory.CompanionTheory.ChamberInd.chamberU | (intros; apply GlobalTheory.CompanionTheory.ChamberInd.chamberU <;> assumption)
