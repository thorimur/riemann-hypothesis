import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelDimGeomConnectedDescendFieldExtension
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothOfRelDim_geomConnected_descend_fieldExtension : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → ∀ D : ℕ, Nonempty X → SmoothOfRelativeDimension D q → GeometricallyConnected q → SmoothOfRelativeDimension D p ∧ GeometricallyConnected p := by
  first | exact @GlobalTheory.FieldDescentSm.smoothOfRelativeDimension_and_geometricallyConnected_descend | exact GlobalTheory.FieldDescentSm.smoothOfRelativeDimension_and_geometricallyConnected_descend | (intros; apply GlobalTheory.FieldDescentSm.smoothOfRelativeDimension_and_geometricallyConnected_descend <;> assumption)
