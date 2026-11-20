import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyDataDescendCountableSubrings
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keyData_descend_countable_subrings : Out.Laws → (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsPrincipalIdealRing R] [CharZero R] (x : KeyIn R) (s : Set R), s.Countable → ∃ (R₀ : Subring R) (_ : IsLocalRing R₀) (_ : IsPrincipalIdealRing R₀) (x₀ : KeyIn R₀), Countable R₀ ∧ s ⊆ R₀ ∧ IsLocalHom R₀.subtype ∧ KeyPB x x₀ R₀.subtype) ∧ KeyDesc := by
  first | exact @GlobalTheory.KeyCountableDescent.keyIn_descends_countable | exact GlobalTheory.KeyCountableDescent.keyIn_descends_countable | (intros; apply GlobalTheory.KeyCountableDescent.keyIn_descends_countable <;> assumption)
