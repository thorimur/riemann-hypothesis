import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalLemmaLatticeDegreeOne
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamentalLemmaLattice_degreeOne : FLAt 1 := by
  first | exact @GlobalTheory.PMon.FLOne.flAt_one | exact GlobalTheory.PMon.FLOne.flAt_one | (intros; apply GlobalTheory.PMon.FLOne.flAt_one <;> assumption)
