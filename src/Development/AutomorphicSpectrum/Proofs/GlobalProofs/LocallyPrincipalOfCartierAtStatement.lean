import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocallyPrincipalOfCartierAt
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_principal_of_cartier_at : ∀ {X : Scheme.{0}} [IsIntegral X] (Z : X.IdealSheafData) (U : X.affineOpens) (q : PrimeSpectrum Γ(X, U.1)), CartAt Z (U.2.fromSpec q) → LocPrincipal (Z.ideal U) q.asIdeal := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.locPrincipal_of_cartAt | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.locPrincipal_of_cartAt | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.locPrincipal_of_cartAt <;> assumption)
