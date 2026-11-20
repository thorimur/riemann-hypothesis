import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCubicalBundleOfSymmetricSemiAbelian
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.exists_cubical_bundle_of_symmetric_semiAbelian : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → ∀ (L : RigLB G) (c : CubicalStr G L), L.IsSymmetric → ∃ P : CP G, P.L = L ∧ HEq P.c c := by
  first | exact @GlobalTheory.UU.exists_cp_of_isSymmetric | exact GlobalTheory.UU.exists_cp_of_isSymmetric | (intros; apply GlobalTheory.UU.exists_cp_of_isSymmetric <;> assumption)
