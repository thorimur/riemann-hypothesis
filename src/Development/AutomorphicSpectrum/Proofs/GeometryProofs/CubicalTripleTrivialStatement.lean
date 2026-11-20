import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CubicalTripleTrivial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.UU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubical_triple_trivial : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → TorusExtension G → ∀ (v : Γ((G ⊗ G ⊗ G).left, ⊤)ˣ), (∀ (T : Over (Sp K)) (x y : T ⟶ G), (lift (1 : T ⟶ G) (lift x y)).left.appTop.hom v.val = 1 ∧ (lift x (lift (1 : T ⟶ G) y)).left.appTop.hom v.val = 1 ∧ (lift x (lift y (1 : T ⟶ G))).left.appTop.hom v.val = 1) → ∀ x y w : 𝟙_ (Over (Sp K)) ⟶ G, (lift x (lift y w)).left.appTop.hom v.val = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CubeUnit.eq_one_at_rational_points | exact GlobalTheory.CompanionTheory.Ar.CubeUnit.eq_one_at_rational_points | (intros; apply GlobalTheory.CompanionTheory.Ar.CubeUnit.eq_one_at_rational_points <;> assumption)
