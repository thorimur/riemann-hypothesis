import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KeyFormulaOfConnFam
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyDatumConnectedFamilyOfPolarizedArithmeticFami
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PolarizedFamilyOfThetaUniformization
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory.KeyFam

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.KeyFam.keyFormula_holds : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.KeyFormula :=
  _root_.GlobalTheory.keyFormula_of_connFam
    (_root_.GlobalTheory.KeyFam.connFam_of_polFam _root_.GlobalTheory.abelianSchemeLaws_all.1
      _root_.GlobalTheory.abelianSchemeLaws_all.2
      (_root_.GlobalTheory.KeyFam.polFam _root_.GlobalTheory.abelianSchemeLaws_all.1 _root_.GlobalTheory.abelianSchemeLaws_all.2
        _root_.GlobalTheory.thetaUnifAV_closed _root_.GlobalTheory.torusAlgebraic_holds))

end GlobalTheory.KeyFam
