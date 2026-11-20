import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineDomainNbhdNormal
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_domain_nbhd_normal : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ (V : X.Opens) (x : X), x ∈ V →
    ∃ U : X.Opens, U ≤ V ∧ x ∈ U ∧ IsAffineOpen U ∧ IsDomain Γ(X, U) := by
  first | exact @GlobalTheory.exists_isAffineOpen_isDomain_of_isNormalScheme | exact GlobalTheory.exists_isAffineOpen_isDomain_of_isNormalScheme | (intros; apply GlobalTheory.exists_isAffineOpen_isDomain_of_isNormalScheme <;> assumption)
