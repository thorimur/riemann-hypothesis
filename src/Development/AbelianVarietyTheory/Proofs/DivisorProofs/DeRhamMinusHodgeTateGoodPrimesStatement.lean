import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamMinusHodgeTateGoodPrimes
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
theorem _root_.GlobalTheory.T.de_rham_minus_hodge_tate_good_primes : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → GlobalTheory.Published.PrismaticDieudonnePerfd → OnObj fun _ O _ _ _ _ => DeRhamMinusHodgeTateGoodPrimesAt O.Y := by
  first | exact @GlobalTheory.DeRhamHodgeTateGoodPrimes.onObj_aux3At_of_knownResults | exact GlobalTheory.DeRhamHodgeTateGoodPrimes.onObj_aux3At_of_knownResults | (intros; apply GlobalTheory.DeRhamHodgeTateGoodPrimes.onObj_aux3At_of_knownResults <;> assumption)
