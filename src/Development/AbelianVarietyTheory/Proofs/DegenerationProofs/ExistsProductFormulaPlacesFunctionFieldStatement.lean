import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProductFormulaPlacesFunctionField
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_productFormulaPlaces_function_field : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (t : K), Transcendental k t → FiniteDimensional (IntermediateField.adjoin k {t}) K → Algebra.IsSeparable (IntermediateField.adjoin k {t}) K → ∃ Pl : Places k K, ∀ x : K, (∀ i, x ∈ Pl.O i) → IsAlgebraic k x := by
  first | exact @GlobalTheory.SS.PlacesExt.exists_places | exact GlobalTheory.SS.PlacesExt.exists_places | (intros; apply GlobalTheory.SS.PlacesExt.exists_places <;> assumption)
