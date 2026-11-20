import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PicardGroupOfFieldTrivial
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.picard_group_of_field_trivial : ∀ (k : Type) [Field k] (c : Pic (Sp k)), c = 0 := by
  first | exact @GlobalTheory.CompanionTheory.PicField.pic_eq_zero | exact GlobalTheory.CompanionTheory.PicField.pic_eq_zero | (intros; apply GlobalTheory.CompanionTheory.PicField.pic_eq_zero <;> assumption)
