import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AffineDomainGenericSpecializes
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_domain_generic_specializes : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (A : X.Opens) (hA : IsAffineOpen A) (p : Cpt ξ), IsCptGen ξ → IsDomain Γ(X, A) → p.1 ∈ A → ∀ z ∈ A, genPt ξ ⤳ z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFrames.genPt_specializes_of_isDomain | exact GlobalTheory.CompanionTheory.Ar.LocFrames.genPt_specializes_of_isDomain | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFrames.genPt_specializes_of_isDomain <;> assumption)
