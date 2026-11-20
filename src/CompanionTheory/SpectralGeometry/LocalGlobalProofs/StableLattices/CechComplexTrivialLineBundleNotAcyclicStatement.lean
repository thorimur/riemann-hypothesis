import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CechComplexTrivialLineBundleNotAcyclic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_complex_trivial_line_bundle_not_acyclic : ∀ {R : Type} [CommRing R] {X : Scheme.{0}} [Nonempty X] (f : X ⟶ Spec (CommRingCat.of R)) (N : LB X)
    (hN : N.IsLB) (hT : Triv N) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → X.Opens) (hc : ⨆ i, D i = ⊤), ¬ (cechLB f N D).Acyclic := by
  first | exact @GlobalTheory.CompanionTheory.PointSurjectivity.not_acyclic_cechLB_of_triv | exact GlobalTheory.CompanionTheory.PointSurjectivity.not_acyclic_cechLB_of_triv | (intros; apply GlobalTheory.CompanionTheory.PointSurjectivity.not_acyclic_cechLB_of_triv <;> assumption)
