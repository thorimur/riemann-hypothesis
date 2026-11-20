import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPowerHigherCohomVanishingPullbackIffPushf
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedPowerHigherCohomVanishing_pullback_iff_pushforward : ∀ {X Y : Scheme.{0}} (g : Y ⟶ X) [IsAffineHom g] (A N : LB X), A.IsLB → N.IsLB → ∀ (G : Y.Modules) [G.IsQuasicoherent], (TwistConeVanishing (A.pull g) (N.pull g) G ↔ TwistConeVanishing A N ((Scheme.Modules.pushforward g).obj G)) := by
  first | exact @GlobalTheory.twistConeVanishing_pull_iff_pushforward | exact GlobalTheory.twistConeVanishing_pull_iff_pushforward | (intros; apply GlobalTheory.twistConeVanishing_pull_iff_pushforward <;> assumption)
