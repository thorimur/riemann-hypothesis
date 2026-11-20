import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SmoothOfRelativeDimensionPowObj

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

theorem powObj_smoothOfRelativeDimension_mul : ∀ (S : Scheme.{0}) (A : Over S) (g j : ℕ),
    SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension (j * g) (Out.powObj A j).hom :=
  fun _ A g j h => smoothOfRelativeDimension_powObj A g h j

end GlobalTheory
