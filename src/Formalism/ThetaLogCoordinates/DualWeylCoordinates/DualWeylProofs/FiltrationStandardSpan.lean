import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.MemSpanStandardIffProjZero
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.FiltrationTheoremOfClauses

noncomputable section

namespace Formalism.InvariantFactorPaths.ColumnFamilies

theorem filtration_standard_span_of : LemmaA → FiltrationStandardSpan :=
  fun hA n _ M CF pi hpi => qb_Mpi_eq hA CF pi hpi

end Formalism.InvariantFactorPaths.ColumnFamilies
