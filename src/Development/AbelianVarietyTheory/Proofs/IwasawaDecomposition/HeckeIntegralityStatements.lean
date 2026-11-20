import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnitNatCastUp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeTransformOfPointLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeReadTie
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmSplitHalves

namespace GlobalTheory.HeckeMember

theorem heckeInt_transform_readTie :
    GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt ∧ GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform ∧ GlobalTheory.HeckeSupSt.HeckeReadTie :=
  ⟨GlobalTheory.HkIntegral.heckeInt,
   GlobalTheory.HeckeEx.heckeTransform_of_pointLaws
     (GlobalTheory.HeckePointLaw.heckePointLaws_of_transport GlobalTheory.ThetaTransport.thetaTransportLaw),
   GlobalTheory.HeckeReadProof.heckeReadTie GlobalTheory.SplitLinear.splitLinearModel GlobalTheory.VacStabFixed.vacFixed⟩

end GlobalTheory.HeckeMember
