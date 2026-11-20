import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricOfHyp
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_of_published_inputs : GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → Hypotheses2 → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → DeepGood → Size → Geom := by
  first | exact @GlobalTheory.CovHt.GeomBound.geom | exact GlobalTheory.CovHt.GeomBound.geom | (intros; apply GlobalTheory.CovHt.GeomBound.geom <;> assumption)
