import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsValuationSubringComplexComapValEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuationSubring_complex_comap_eq : ∀ (F : IntermediateField ℚ ℂ) (U : ValuationSubring F) (p : ℕ), (p : F) ∈ U.nonunits → ∃ W : ValuationSubring ℂ, (p : ℂ) ∈ W.nonunits ∧ W.comap F.val.toRingHom = U := by
  first | exact @GlobalTheory.exists_valuationSubring_complex_comap_val_eq | exact GlobalTheory.exists_valuationSubring_complex_comap_val_eq | (intros; apply GlobalTheory.exists_valuationSubring_complex_comap_val_eq <;> assumption)
