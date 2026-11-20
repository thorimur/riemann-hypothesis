import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BaseChangeDescent.Strong
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeak
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.SplitRigidity.SplitRigid
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.BaseChangeNB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.SaturatedBaseChange.SpehSingleFactorEquiv
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatchOfMatchOffTEmpty
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.NarrowSwap

open UpperTheory.V.Z.Tf PositivityTheory.AutomorphicGaloisHodgeTate.SaturatedBaseChange

namespace UpperTheory.Gal.Desc

theorem speh : GlobalTheory.BcSpeh.BcSpeh := UpperTheory.BaseChangeIdentities.speh UpperTheory.BaseChangeIdentities.baseChangeNB

theorem weakAll : WeakAll := weakAll_of SR.splitRigid (GaloisFromTraceFormula.partNorm GaloisFromTraceFormula.absInf) GOne.unitOf GaloisFromTraceFormula.runTh

theorem desc : GlobalTheory.Cong.Desc :=
  desc_of speh compUnique oneFactor PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound PositivityTheory.jumpWindows.cuspidalMultiplicityOne SR.splitRigid GOne.thin GOne.unitOf weakAll

theorem descOffT : GlobalTheory.Cong.DescOffT := GlobalTheory.Cong.descOffT_of_desc desc

end UpperTheory.Gal.Desc
