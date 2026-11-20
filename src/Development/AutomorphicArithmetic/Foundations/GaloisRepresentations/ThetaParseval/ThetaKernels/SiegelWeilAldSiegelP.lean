import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldSiegel
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DiagonalColumns.AdChar

set_option synthInstance.maxHeartbeats 200000

section
namespace PositivityTheory.SiegelWeilFormula.Ald
theorem siegelSmall_of_slice_k (hF : SliceFacts) : _root_.PositivityTheory.SiegelWeilFormula.Ald.SiegelSmall_k := _root_.PositivityTheory.SiegelWeilFormula.Ald.siegelSmall_of_k hF Ldx.adaptedChar
end PositivityTheory.SiegelWeilFormula.Ald
end
