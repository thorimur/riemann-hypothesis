import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.MemClosureOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.AbsNe
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ProjEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.AbsIso
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGHgtFst
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGRealPair
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGNonVan
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGRallis
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGBumpAny
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGTail
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGSchurStep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGLiftAut
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGReadLift

set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.TP
theorem tLift_of_tools_k (T : _root_.UpperTheory.TP.Tools_k) (hH : _root_.GlobalTheory.ThK.Dbl.HgtEx_k) : _root_.UpperTheory.TP.TLift_k :=
  _root_.UpperTheory.TP.tLift_of_k T hH brEx (_root_.UpperTheory.TP.hgtFst_k T) (_root_.UpperTheory.TP.realPair_k T)
    (_root_.UpperTheory.TP.nonVan_k T (_root_.UpperTheory.TP.rallis_k T) (_root_.UpperTheory.TP.decomp_k T) (_root_.UpperTheory.TP.bumpAny_k T) (_root_.UpperTheory.TP.datum_k T) (_root_.UpperTheory.TP.tail_k T) absNe (_root_.UpperTheory.TP.schurStep_k T)) (_root_.UpperTheory.TP.liftAut_k T) projEx
    (_root_.UpperTheory.TP.readLift_k T (_root_.UpperTheory.TP.liftAut_k T) absIso)
end UpperTheory.TP
end
