import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.Ci
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.GmOfBcfl
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CoreLift
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.LiftAll
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.LiftStep
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.BcflUnit

theorem UpperTheory.ConvolutionTheory.Sph.gm : UpperTheory.ConvolutionTheory.GM.GM := UpperTheory.ConvolutionTheory.GM.gm_of_bcfl PositivityTheory.Rg.Tf.Loc.bcflUnit

theorem UpperTheory.ConvolutionTheory.Sph.liftAll : UpperTheory.ConvolutionTheory.T.LiftAll :=
  UpperTheory.ConvolutionTheory.T.liftAll (UpperTheory.ConvolutionTheory.T.liftStep (UpperTheory.ConvolutionTheory.T.coreLift UpperTheory.ConvolutionTheory.ci UpperTheory.ConvolutionTheory.Sph.gm))
