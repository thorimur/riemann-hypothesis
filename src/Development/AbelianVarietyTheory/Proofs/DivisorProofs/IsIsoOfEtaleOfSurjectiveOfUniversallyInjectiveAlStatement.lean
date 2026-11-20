import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfEtaleOfSurjectiveOfUniversallyInjectiveAl
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIso_of_etale_of_surjective_of_universallyInjective' : ∀ (X Z : Scheme.{0}) (h : X ⟶ Z), Etale h → Surjective h → UniversallyInjective h → IsIso h := by
  first | exact @GlobalTheory.Mum.isIso_of_etale_of_surjective_of_universallyInjective | exact GlobalTheory.Mum.isIso_of_etale_of_surjective_of_universallyInjective | (intros; apply GlobalTheory.Mum.isIso_of_etale_of_surjective_of_universallyInjective <;> assumption)
