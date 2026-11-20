import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitTop
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.SoCoinvariantsOfBernstein
import Development.WeilBound.ThetaLifts.LocalTheory.DixmierCommutants.RamifiedMultiplicityOneOfBernstein
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.KCoinvOfDict
import Development.WeilBound.ThetaLifts.CartanFactorisation.AdmDef
import Development.WeilBound.ThetaLifts.CartanFactorisation.Factor
import Development.WeilBound.ThetaLifts.CartanFactorisation.MaxDef
import Development.WeilBound.ThetaLifts.CartanFactorisation.PolCountDef
import Development.WeilBound.ThetaLifts.CartanFactorisation.UnitDef
import Development.WeilBound.ThetaLifts.Reductions.JoinDef

namespace PositivityTheory.ThKR

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

structure SplitFacts : Prop where
  kCoinv : PositivityTheory.KCo.DictSt → GlobalTheory.ThK.KCoinv
  soCoinv : GlobalTheory.ThK.KFin → PositivityTheory.ThKF.SoCoinv
  ramifiedMultiplicityOne : PositivityTheory.ThKG.Loc.RamifiedMultiplicityOne
  finRam : PositivityTheory.ThK.FinRam
  finSplit : PositivityTheory.ThK.FinSplit

def MaxSteps : Prop :=
  ∃ M : Prop, (PositivityTheory.ThKF.LocUPairEx → PositivityTheory.KCo.DictSt → M) ∧
    (PositivityTheory.ThKR.JoinTri → M → PositivityTheory.ThKF.ArchOp → PositivityTheory.ThKF.ArchLie → PositivityTheory.ThKF.ArchUniq → PositivityTheory.ThKF.PolCount →
      PositivityTheory.ThKF.CartanConj → PositivityTheory.ThKF.CartanMove → GlobalTheory.ThK.KCoinv → PositivityTheory.ThKF.ILeft → GlobalTheory.ThK.PolRe) ∧
    (GlobalTheory.ThK.ThetaBasic → GlobalTheory.ThK.WeilConv → GlobalTheory.ThK.SoCont → GlobalTheory.ThK.SqInt → GlobalTheory.ThK.KDecay → GlobalTheory.ThK.KCoinv →
      PositivityTheory.ThKF.ICont → PositivityTheory.ThKF.ArchOp → PositivityTheory.ThKF.ArchLie → PositivityTheory.ThKF.ArchUniq → PositivityTheory.ThKF.RadMax → PositivityTheory.ThKF.AdmTri → M →
      PositivityTheory.ThKR.JoinTri → PositivityTheory.ThKF.SoCoinv → PositivityTheory.ThKF.Kills)

theorem splitFacts_of (h : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) : SplitFacts :=
  ⟨PositivityTheory.KCo.kCoinv_of_dict h, PositivityTheory.KCo.so_coinvariants_of_bernstein h, PositivityTheory.ThKG.LocalRamifiedLeviRestriction.ramifiedMultiplicityOne_of_bernstein h, PositivityTheory.ThK.SplitAsm.finite_ramified_of_bernstein h,
    PositivityTheory.ThK.SplitAsm.finite_split_holds h⟩

end PositivityTheory.ThKR
