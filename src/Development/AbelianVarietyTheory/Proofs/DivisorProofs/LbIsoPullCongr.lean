import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedLineBundlesCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.CxPts GlobalTheory.Points
open scoped CategoryTheory.Obj
open GlobalTheory.MBLit

noncomputable section

namespace GlobalTheory.MBDesc

theorem lbIso_pullComp {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (g : Z ⟶ Y) :
    LBIso (L.pull (g ≫ f)) ((L.pull f).pull g) :=
  LBIso.chartPull (RigidBundleGlue.chartPullComp L f g _ rfl) (chartPullId _)
    ⟨idIso _, idIso_isGen (pull_isLB (pull_isLB hL f) g)⟩

theorem lbIso_pull_congr {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {f g : Y ⟶ X} (h : f = g) :
    LBIso (L.pull f) (L.pull g) := h ▸ ⟨idIso _, idIso_isGen (pull_isLB hL f)⟩

end GlobalTheory.MBDesc
