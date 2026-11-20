import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsEqOfSpMapSubtypeCompEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_spMap_subtype_comp_eq_of_isSeparated : ∀ (R : Type) [CommRing R] (R₀ : Subring R) (X : Scheme.{0}) (p : X ⟶ Sp R₀) [IsSeparated p] (x y : Sp R₀ ⟶ X), x ≫ p = y ≫ p → spMap R₀.subtype ≫ x = spMap R₀.subtype ≫ y → x = y := by
  first | exact @GlobalTheory.sections_eq_of_spMap_subtype_comp_eq | exact GlobalTheory.sections_eq_of_spMap_subtype_comp_eq | (intros; apply GlobalTheory.sections_eq_of_spMap_subtype_comp_eq <;> assumption)
