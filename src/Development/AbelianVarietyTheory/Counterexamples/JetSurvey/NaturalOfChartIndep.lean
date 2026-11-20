import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThValDescIn
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaExprBaseChangeTest

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj
  Formalism.MainNotions.ModuliIntegralCharts.H1

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

theorem frBCField : FrBCFieldSt Xo c := fun S _ _ y K _ _ ψ =>
  GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c S K ψ y

end GlobalTheory.ThetaExprBaseChangeTest
