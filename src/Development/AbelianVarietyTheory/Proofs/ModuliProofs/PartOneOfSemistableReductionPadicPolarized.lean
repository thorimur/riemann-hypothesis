import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PartIOfSemistableReductionOfArcFam
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsArcFamilyPointWithFramesProof
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
open scoped CategoryTheory.Obj in

theorem _root_.GlobalTheory.partI_of_semistableReduction :
    _root_.GlobalTheory.Published.SemistableReductionSt → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PartI := fun h =>
  _root_.GlobalTheory.partI_of_semistableReduction_of_arcFam h _root_.GlobalTheory.arcFam_closed

end GlobalTheory
