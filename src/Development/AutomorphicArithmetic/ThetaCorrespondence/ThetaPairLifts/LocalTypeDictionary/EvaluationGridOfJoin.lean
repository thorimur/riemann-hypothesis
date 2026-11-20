import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsWeilDeligneOfLocalInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedLinearBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaPairLiftCuspidalOfHypotheses
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedBaseExistence
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedConstantExistence
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RowSumOfHyp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedDictionaryEventuallyLarge
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistRatioMemNumberField
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomFieldIsNumberField
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesisBundleConversions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomRankSumLeTwoMulTotalRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatRepr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioConjugatesOfTransport
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralAndArchimedeanBounds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyLargeGrid
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridExistenceOfPieces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeyFinitenessGlobal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormFieldSquareClass
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraceSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CarrySecond
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CarryWeilUnitaryPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsExOfSeparates
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIntegralOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KeyFinHolds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalFormCharacters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalFormJets
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalFormPhase
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeAlgebraMapMono
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TrEasy
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TrJetOfTrFlip
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TrPhaseOfTrFlip
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransferBottom
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransferFlip
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwoLeMOf

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open GlobalTheory.Mem.Top GlobalTheory.Mem.LiteralAutomorphy
namespace GlobalTheory.Mem.LiteralAutomorphy
theorem evaluation_grid_of_join : GlobalTheory.Published.HoweDualityReal → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.Mem.LiteralAutomorphy.JoinOut → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate → ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → EvLgG (GridA CF) :=
  fun hw hm P hJ ht K WC LM TA FS =>
    GlobalTheory.Mem.LiteralAutomorphy.evLgG_gridA_of_exGrid
      (GlobalTheory.Mem.LiteralAutomorphy.exGrid_of (_root_.GlobalTheory.Mem.LiteralAutomorphy.exists_weilDeligne_of_localInputs P)
        (isEx_of_separates FS (_root_.GlobalTheory.RowEx.twisted_linear_bound P (_root_.GlobalTheory.PairLift.thetaPairLift_cuspidal_of_hypotheses P)) (_root_.GlobalTheory.RowEx.twisted_base_existence P (_root_.GlobalTheory.RowEx.twisted_constant_existence hw hm P K WC LM TA)))
        (nfAll_of GlobalTheory.RowEx.nfChars nfRoot (GlobalTheory.RowEx.nfPhase_of_sumOKK (_root_.GlobalTheory.RowClaim.rowSum_of_hypotheses_alt P))
          (GlobalTheory.NFJetProof.nfJet_holds (_root_.GlobalTheory.RowClaim.rowSum_of_hypotheses_alt P) GlobalTheory.NormSum.inp_all (_root_.GlobalTheory.DictFree.twisted_dictionary_eventually_large P GlobalTheory.NormSum.inp_all))
          (_root_.GlobalTheory.RowEx.RatioField.twistRatio_mem_numberField P
            (GlobalTheory.ToricTransport.toricRatioConjugates_of_transport
              hJ.2.2.1)
            GlobalTheory.SqTop.fieldDat
            (GlobalTheory.SqTop.lNe_of_functionalEquation (GlobalTheory.Published.HeckeTateFunctionalEquation.abs ht) GlobalTheory.HeckeStrip.completedLBoundedInStrips
              GlobalTheory.SqTop.fieldDat))
          (_root_.GlobalTheory.RowEx.bottomField_isNumberField P GlobalTheory.NormSum.inp_all))
        (GlobalTheory.Mem.LiteralAutomorphy.nfSq_of_fieldDat GlobalTheory.NormSum.intSt_and_archSt.1 GlobalTheory.SqTop.fieldDat
          (GlobalTheory.ToricExist.torEx hJ.2.1 GlobalTheory.SqTop.fieldDat
            (GlobalTheory.SqTop.lNe_of_functionalEquation (GlobalTheory.Published.HeckeTateFunctionalEquation.abs ht) GlobalTheory.HeckeStrip.completedLBoundedInStrips
              GlobalTheory.SqTop.fieldDat))
          GlobalTheory.SqTop.BotSmallProof.botSmall_holds)
        CarryGrid.carryG (GlobalTheory.RowEx.carryW_of_weil P.weilRepresentationUnitaryPair) GlobalTheory.RowEx.carryS trEasy
        (PhaseCarry.trPhase_of_trFlip GlobalTheory.RowEx.Carry.flippedTensorsTransferToGrid_proof) (Jet.trJet_of_trFlip GlobalTheory.RowEx.Carry.flippedTensorsTransferToGrid_proof) GlobalTheory.RowEx.trBot_holds
        GlobalTheory.Mem.LiteralAutomorphy.trSq_holds keyFin_holds GlobalTheory.Mem.LiteralAutomorphy.gKeyFin)
end GlobalTheory.Mem.LiteralAutomorphy
end
