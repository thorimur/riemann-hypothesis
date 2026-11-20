import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverBaseChangeOfProperQuasiProjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProjOver_baseChange_of_proper_quasiProjective : ∀ (R A : Type) [CommRing R] [CommRing A] (S : Scheme.{0}) (s : S ⟶ Sp R) (G : Over S) (y : Sp A ⟶ S) (B : Over (Sp A)) (φ : B.left ⟶ G.left), IsProper G.hom → IsQProjOver (G.hom ≫ s) → IsPullback φ B.hom G.hom y → IsProjOver B.hom := by
  first | exact @GlobalTheory.isProjOver_of_isPullback_of_isProper_of_isQProjOver | exact GlobalTheory.isProjOver_of_isPullback_of_isProper_of_isQProjOver | (intros; apply GlobalTheory.isProjOver_of_isPullback_of_isProper_of_isQProjOver <;> assumption)
