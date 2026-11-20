import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldSmallS
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.HaarLc

set_option synthInstance.maxHeartbeats 200000

section
namespace PositivityTheory.SiegelWeilFormula.Ald
theorem smallS_of'_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.ChartFacts_k → SliceFacts → _root_.PositivityTheory.SiegelWeilFormula.Ald.SmallS_k := fun hC hF => _root_.PositivityTheory.SiegelWeilFormula.Ald.smallS_of_k hC hF (subSplit_of hF) haarLc
end PositivityTheory.SiegelWeilFormula.Ald
end
