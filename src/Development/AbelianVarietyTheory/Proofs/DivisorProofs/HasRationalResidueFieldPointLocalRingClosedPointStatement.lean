import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasRationalResidueFieldPointLocalRingClosedPoint
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasRationalResidueField_pointLocalRing_closedPoint : ∀ (Z : Scheme.{0}) [IsIntegral Z] (q : Z ⟶ Sp ℂ) [LocallyOfFiniteType q] (y : Z), IsClosed ({y} : Set Z) → RatRes (GlobalTheory.Cartier.constFn q) (locRing y) := by
  first | exact @GlobalTheory.FieldPair.ratRes_locRing_of_isClosed | exact GlobalTheory.FieldPair.ratRes_locRing_of_isClosed | (intros; apply GlobalTheory.FieldPair.ratRes_locRing_of_isClosed <;> assumption)
