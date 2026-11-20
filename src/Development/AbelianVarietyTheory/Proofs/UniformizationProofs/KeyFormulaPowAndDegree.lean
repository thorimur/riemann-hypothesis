import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyRuleCharHalf
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.FiniteAbsLeOneMulMemRange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormLeTsumOfCubeFourierCoeffLe
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TorusAlgebraicHolds
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFormulaPowOfKeyRuleCharZero
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FromBlocksMapIntCastMemSymplecticGroup
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaUniformisationComplexAbelianVarieties

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.keyFormulaPow_and_keyDegree :
    _root_.GlobalTheory.KeyFormulaPow ∧ _root_.GlobalTheory.KeyDegreeSt := by
  obtain ⟨N, hN, hrule⟩ := _root_.GlobalTheory.KeyTop.exists_keyRule_charHalf
    _root_.GlobalTheory.abelianSchemeLaws_all.1 _root_.GlobalTheory.thetaUnifAV_closed
    _root_.GlobalTheory.inversionStatement_holds
    (_root_.GlobalTheory.phHolo_of_phKoecher _root_.GlobalTheory.phKoecher)
    _root_.GlobalTheory.torusAlgebraic_holds
  have hpow : _root_.GlobalTheory.KeyFormulaPow :=
    _root_.GlobalTheory.KeyPow.keyFormulaPow_of_keyRule _root_.GlobalTheory.thetaUnifAV_closed
      N hN hrule
  exact ⟨hpow, _root_.GlobalTheory.keyDegree_of_keyFormulaPow hpow⟩

end GlobalTheory
