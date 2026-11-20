import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSymplecticCoordinatesOfIsPeriod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.PeriodRank

theorem finrank_la_eq_two_mul :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ)
      (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)), IsPeriod D ty P →
      Module.finrank ℤ D.La = 2 * g :=
  fun _ _ _ _ _ _ _ _ _ hP => (GlobalTheory.FibreExp.free_finite_finrank_of_isPeriod hP).2.2

end GlobalTheory.CompanionTheory.Ar.Flat.PeriodRank
