import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointFlatOfModificationOfDomain
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericPoint_flat_of_modification_of_domain : ∀ (R : Type) [CommRing R] [IsDomain R] (M : GlobalTheory.Mum.Modif R), Flat M.gp := by
  first | exact @GlobalTheory.Mum.Modif.flat_gp | exact GlobalTheory.Mum.Modif.flat_gp | (intros; apply GlobalTheory.Mum.Modif.flat_gp <;> assumption)
