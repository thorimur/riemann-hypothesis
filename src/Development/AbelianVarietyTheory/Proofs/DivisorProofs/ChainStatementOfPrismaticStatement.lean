import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainStatementOfPrismatic
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
theorem _root_.GlobalTheory.T.chain_statement_of_prismatic : GlobalTheory.CovTop.HypothesesXH → GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.PrismaticDieudonnePerfd → ChainSt := by
  first | exact @GlobalTheory.MixedLocalChains.chainSt | exact GlobalTheory.MixedLocalChains.chainSt | (intros; apply GlobalTheory.MixedLocalChains.chainSt <;> assumption)
