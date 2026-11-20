import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFiniteKerOfSurjPointsSameDimension
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFinite_ker_of_surj_points_same_dimension : ∀ (k : Type) [Field k] [IsAlgClosed k] (G G' : Over (Sp k)) [GrpObj G] [GrpObj G'] (g : ℕ), SmConn G → SmConn G' → SmoothOfRelativeDimension g G.hom → SmoothOfRelativeDimension g G'.hom → ∀ i : G ⟶ G', IsMonHom i → (∀ y : (𝟙_ (Over (Sp k)) ⟶ G'), ∃ x : (𝟙_ (Over (Sp k)) ⟶ G), x ≫ i = y) → IsFinite (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G')).left := by
  first | exact @GlobalTheory.SS.isFinite_ker_of_surjective_points_of_dim_eq | exact GlobalTheory.SS.isFinite_ker_of_surjective_points_of_dim_eq | (intros; apply GlobalTheory.SS.isFinite_ker_of_surjective_points_of_dim_eq <;> assumption)
