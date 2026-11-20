import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DualCoefSpaceIsTensorOverRealPlacesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopSeparationStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.SepGap
import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.RankLeOneOfDep
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGapAlt

namespace UpperTheory.Lit

open GlobalTheory.SepRows

theorem burGapPos : Bur.BurGapPos := Bur.BurPos.burGapPos_of_bmu CompanionTheory.Bmu.besselMapUniqGap

theorem separate_of_steps_gap (P : GlobalTheory.FunPr.Hypotheses₂) (hT : RowTower) :
    SizeGap → GoodRows → RowConv → WeakSep → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate :=
  Bur.separate_of_burGapPos burGapPos GlobalTheory.T.dualCoefSpace_isTensorOverRealPlaces (GlobalTheory.T.top_separation P) hT

end UpperTheory.Lit
