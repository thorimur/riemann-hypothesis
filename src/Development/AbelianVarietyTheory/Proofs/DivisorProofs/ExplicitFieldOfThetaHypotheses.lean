import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioConjugatesOfTransport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseExOf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwoLeMOf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExFieldOfKeyFinExKey
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsExOfSeparates
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExKeyOf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KeyFinHolds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeAlgebraMapMono
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIntegralOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TrEasy
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TrJetOfTrFlip
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TrPhaseOfTrFlip
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSumOfHyp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftsCuspidalOfFunctoriality
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CarrySecond
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CarryWeilUnitaryPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstantTermExistenceFromHowe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DictionarySizeBound
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridExistenceOfFunctoriality
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearIndependenceFromLifts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalFormBottom
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalFormCharacters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalFormJets
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalFormPhase
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalFormToricRatio
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransferBottom
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransferFlip
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaNormBoundHypothesesSatisfied
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesisBundleConversions

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory.RowEx

theorem exField_of_join : GlobalTheory.Published.HoweDualityReal → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Mem.LiteralAutomorphy.JoinOut → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate → ExField :=
  fun hw hm P hJ ht K WC LM TA FS =>
    exField_of_keyFin_exKey keyFin_holds
      (exKey_of (GlobalTheory.RowEx.gridEx_of_hypotheses P)
        (isEx_of_separates FS (GlobalTheory.RowEx.linB P (GlobalTheory.PairLift.liftsCuspidal_of_classicalTheorems P)) (baseEx_of P (GlobalTheory.RowEx.constEx_of hw hm P K WC LM TA)))
        (nfAll_of GlobalTheory.RowEx.nfChars nfRoot (GlobalTheory.RowEx.nfPhase_of_sumOKK (GlobalTheory.RowClaim.rowSum_of_hypotheses P))
          (GlobalTheory.NFJetProof.nfJet_holds (GlobalTheory.RowClaim.rowSum_of_hypotheses P) GlobalTheory.NormSum.inp_all (GlobalTheory.DictFree.dictAt_big P GlobalTheory.NormSum.inp_all))
          (GlobalTheory.RowEx.RatioField.nfRatio P
            (GlobalTheory.ToricTransport.toricRatioConjugates_of_transport
              hJ.2.2.1)
            GlobalTheory.SqTop.fieldDat
            (GlobalTheory.SqTop.lNe_of_functionalEquation (GlobalTheory.Published.HeckeTateFunctionalEquation.abs ht) GlobalTheory.HeckeStrip.completedLBoundedInStrips
              GlobalTheory.SqTop.fieldDat))
          (GlobalTheory.RowEx.nfBot_holds P GlobalTheory.NormSum.inp_all))
        CarryGrid.carryG (GlobalTheory.RowEx.carryW_of_weil P.weilRepresentationUnitaryPair) GlobalTheory.RowEx.carryS trEasy
        (PhaseCarry.trPhase_of_trFlip GlobalTheory.RowEx.Carry.flippedTensorsTransferToGrid_proof) (Jet.trJet_of_trFlip GlobalTheory.RowEx.Carry.flippedTensorsTransferToGrid_proof) GlobalTheory.RowEx.trBot_holds)

end GlobalTheory.RowEx
