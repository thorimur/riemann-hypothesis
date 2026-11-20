import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueKnownOfPolarizedPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFrameValueKnown_of_polarizedPullback : Out.Laws → ∀ (K : Type) [Field K] (y y' : KeyIn K) (φ : y'.P.A.left ⟶ y.P.A.left), PolPB y'.P y.P (𝟙 _) φ → Known K y → Known K y' := by
  first | exact @GlobalTheory.KnownScale.known_of_polPB | exact GlobalTheory.KnownScale.known_of_polPB | (intros; apply GlobalTheory.KnownScale.known_of_polPB <;> assumption)
