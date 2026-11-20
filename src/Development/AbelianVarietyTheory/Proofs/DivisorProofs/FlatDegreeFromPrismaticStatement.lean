import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeFromPrismatic
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_degree_from_prismatic : GlobalTheory.Published.ScholzeWeinsteinB → GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension → GlobalTheory.Published.PrismaticDieudonneHodge → FlatDegreeSt := by
  first | exact @GlobalTheory.FlatCore.flatDegreeSt_of_prismaticDieudonne | exact GlobalTheory.FlatCore.flatDegreeSt_of_prismaticDieudonne | (intros; apply GlobalTheory.FlatCore.flatDegreeSt_of_prismaticDieudonne <;> assumption)
