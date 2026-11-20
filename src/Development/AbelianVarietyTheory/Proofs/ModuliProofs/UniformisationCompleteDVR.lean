import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisationCompleteDvrOfLaws
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in

theorem _root_.GlobalTheory.uniformisation_dvr_unconditional : _root_.GlobalTheory.LN.USt :=
  _root_.GlobalTheory.LN.uniformisation_dvr _root_.GlobalTheory.allSixLaws.1
    _root_.GlobalTheory.allSixLaws.2.1 _root_.GlobalTheory.allSixLaws.2.2.1
    _root_.GlobalTheory.allSixLaws.2.2.2.1 _root_.GlobalTheory.allSixLaws.2.2.2.2.1

end GlobalTheory
