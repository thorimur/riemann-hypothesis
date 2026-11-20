import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CycFree
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.QuadBC2
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.AbsNormConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPCohC
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SVPatch
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.DefQuatExists
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GelfandKazhdanReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformRepOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.PCuspSS
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClozelCohomology.ClozelConjC

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Formalism.GaloisCohomology UpperTheory.Top
namespace UpperTheory.V.HV.DescentVanishingReductions
open UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Lit UpperTheory.V.Z.Bc
theorem published_hypotheses_from_patching_alt (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (desc : Z.Desc.DescWeak) : _root_.UpperTheory.V.Af.HypothesesH' :=
  { litN := hN, cohC := _root_.UpperTheory.V.Af.clozelCohC_alt hN, conjC := Z.Coh.clozelConjC, borelC := Z.Coh.borelInjC,
    galR := _root_.UpperTheory.Gal.SV.galois_rep_exists_totally_real_rank_two_of_base_change hN UpperTheory.ConvolutionTheory.R2.quadBC2 admissibleReal, smoR := strongMultOneReal,
    gkR := gelfandKazhdanReal strongMultOneReal, admR := admissibleReal, bc := Br.quadBC0_of_two UpperTheory.ConvolutionTheory.R2.quadBC2,
    newform := newformRepOf cuspSemisimpleReal admissibleReal,
    descU := desc, cyc := cycC_holds, cyc2 := Or.inl UpperTheory.ConvolutionTheory.RankTwoDescent.descS, quat := defQuatExists, ssR := cuspSemisimpleReal }
end UpperTheory.V.HV.DescentVanishingReductions
end
