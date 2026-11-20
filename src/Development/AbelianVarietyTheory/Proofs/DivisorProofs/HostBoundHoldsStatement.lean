import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.host_bound_holds : ∀ M : ℝ, HostN M := by
  first | exact @GlobalTheory.CovTop.Sizes.hostN | exact GlobalTheory.CovTop.Sizes.hostN | (intros; apply GlobalTheory.CovTop.Sizes.hostN <;> assumption)
