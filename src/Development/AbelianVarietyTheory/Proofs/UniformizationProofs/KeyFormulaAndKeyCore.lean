import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.DetValuationLeOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KeyFormulaOfConnFam
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ConnFamHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory

theorem keyFormula_and_keyCore : KeyFormula ∧ Formalism.L2.LamCM.KeyCore :=
  ⟨GlobalTheory.keyFormula_of_connFam GlobalTheory.KeyFam.connFam_holds, Formalism.L2.LamCM.key_formula_link (GlobalTheory.keyFormula_of_connFam GlobalTheory.KeyFam.connFam_holds)⟩

end GlobalTheory
