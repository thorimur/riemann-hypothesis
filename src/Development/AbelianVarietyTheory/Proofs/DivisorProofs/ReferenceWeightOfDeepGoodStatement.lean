import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceWeightOfDeepGood
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reference_weight_of_deep_good : Hypotheses2 → DeepGood → Size → FlatDeg → RefW := by
  first | exact @GlobalTheory.RefSum.refW_of_size | exact GlobalTheory.RefSum.refW_of_size | (intros; apply GlobalTheory.RefSum.refW_of_size <;> assumption)
