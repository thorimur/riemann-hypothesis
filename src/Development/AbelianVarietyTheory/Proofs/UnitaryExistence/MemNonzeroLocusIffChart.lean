import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.AbVarProj

section General
variable {X Y : Scheme.{0}} {L : LB X}

theorem mem_nonzeroLocus_iff_sval {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (y : Y) {J : (Y ⟶ X) → L.ι} (hJ : Good L y J) :
    y ∈ nonzeroLocus s ↔ IsUnit (sval s (𝟙 Y) y J) := by
  refine ⟨fun h => ?_, fun h => (mem_nonzeroLocus s y).2 ⟨_, hJ.mem φ (𝟙 Y), h⟩⟩
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  exact isUnit_sval s (𝟙 Y) y hJ k hk

end General

section Group
variable {S : Scheme.{0}} (A : Over S) [GrpObj A]

end Group

end GlobalTheory.AbVarProj
end
