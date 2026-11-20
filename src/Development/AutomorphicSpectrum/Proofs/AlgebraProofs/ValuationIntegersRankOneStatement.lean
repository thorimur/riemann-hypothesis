import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ValuationIntegersRankOne

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_integers_rank_one : ∀ (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R →
    ∃ (_ : IsDomain R), ValuationRing R ∧ Ring.DimensionLEOne R ∧ IsFractionRing R C := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin.integers_valuationRing_dimensionLEOne_isFractionRing | exact GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin.integers_valuationRing_dimensionLEOne_isFractionRing | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin.integers_valuationRing_dimensionLEOne_isFractionRing <;> assumption)
