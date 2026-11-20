import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem datum_exists_period :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ)
      (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty → ∃ P, IsPeriod D ty P :=
  fun E _ _ _ H D g ty hty => PeriodNonempty.exists_isPeriod E H D g ty hty

end GlobalTheory
