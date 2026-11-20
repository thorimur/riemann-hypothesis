import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LogDerivSeriesOfExplicit
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_deriv_series_of_explicit : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → Formalism.HermitianLattices.GL2a2.LogDerivSeries := by
  first | exact @GlobalTheory.MangoldtSeries.logDerivSeries | exact GlobalTheory.MangoldtSeries.logDerivSeries | (intros; apply GlobalTheory.MangoldtSeries.logDerivSeries <;> assumption)
