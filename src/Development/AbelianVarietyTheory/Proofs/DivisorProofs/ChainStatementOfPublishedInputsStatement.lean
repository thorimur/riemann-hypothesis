import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainStatementOfPublishedInputs
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
theorem _root_.GlobalTheory.T.chainW_of_alteration_prismatic : GlobalTheory.CovTop.HypothesesXH → GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.RegularAlteration → GlobalTheory.Published.ScholzeWeinsteinB → GlobalTheory.Published.PrismaticDieudonnePerfd → ChainWSt := by
  first | exact @GlobalTheory.BundleChernComparison.chainWSt | exact GlobalTheory.BundleChernComparison.chainWSt | (intros; apply GlobalTheory.BundleChernComparison.chainWSt <;> assumption)
