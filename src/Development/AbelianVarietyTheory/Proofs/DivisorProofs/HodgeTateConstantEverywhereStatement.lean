import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateConstantEverywhere
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_constant_everywhere : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension → GlobalTheory.Published.PrismaticDieudonneHodge → Always fun U x => HTConst U x := by
  first | exact @GlobalTheory.FlatCore.htConst_always | exact GlobalTheory.FlatCore.htConst_always | (intros; apply GlobalTheory.FlatCore.htConst_always <;> assumption)
