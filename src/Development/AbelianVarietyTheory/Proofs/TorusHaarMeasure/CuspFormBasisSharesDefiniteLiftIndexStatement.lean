import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CuspFormBasisSharesDefiniteLiftIndex
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormBasisShares_definite_liftIndex : SharesDefSt := by
  first | exact @GlobalTheory.SharesDefinite.sharesDef | exact GlobalTheory.SharesDefinite.sharesDef | (intros; apply GlobalTheory.SharesDefinite.sharesDef <;> assumption)
