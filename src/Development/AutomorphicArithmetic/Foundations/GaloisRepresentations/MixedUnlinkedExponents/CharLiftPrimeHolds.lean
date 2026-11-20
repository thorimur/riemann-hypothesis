import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.LpEvalZero
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.LpPowOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.ChsFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.ValsExtOfAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.FdegEq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.TwValsOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.GamSumOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.GamOneOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.NmEq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.ChsConsSome
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.SplitSuppOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.RkSupp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.RkLiftOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.UpThruOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.CharLiftPrimeOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.MatchBCX
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.WeakStableAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CoreDesc
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.DescStep
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStrong

namespace UpperTheory.Gal.GamX

open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.T

theorem gamSum_holds : GamSum :=
  gamSumOf matchBCX normCnt normVal (lpPowOf lpInj) chsFacts fdegEq (twValsOf normVal)

theorem gamOne_holds : GamOne := gamOneOf chsFacts (valsExtOf polFacts) gamSum_holds

theorem splitSupp_holds : SplitSupp :=
  splitSuppOf nmEq suppFacts Sph.weakStable
    (splitStrong (descStep (coreDesc ci Sph.gm) (liftAll (liftStep (coreLift ci Sph.gm)))))

theorem gamMixed_holds : GamMixed :=
  gamMixed_of gamOne_holds splitSupp_holds chsTr rkSupp (rkLiftOf UpperTheory.V.Z.Gam.normLoc) (upThruOf chsFacts)

theorem charSupp_holds : CharSupp := charSupp_of gamMixed_holds nmEq suppFacts

theorem charLiftPrime_holds : CharLiftPrime := charLiftPrime_of charSupp_holds

end UpperTheory.Gal.GamX
