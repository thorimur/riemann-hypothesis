import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsColimitSpecQuotientComplementaryIdempotents
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isColimit_spec_quotient_complementary_idempotents : ∀ (R : Type) [CommRing R] (e e' : R), IsIdempotentElem e → e + e' = 1 → Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk (spMap (Ideal.Quotient.mk (Ideal.span {e}))) (spMap (Ideal.Quotient.mk (Ideal.span {e'}))))) := by
  first | exact @GlobalTheory.specQuotIdemCoprod | exact GlobalTheory.specQuotIdemCoprod | (intros; apply GlobalTheory.specQuotIdemCoprod <;> assumption)
