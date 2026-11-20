import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UwRQeIsNsmul
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT.Cl

theorem galois_holds : AllU fun {_} _ _ {_} {_} {_} {_} _ _ U => Cl.Galois U := by
  intro R _ _ _ I hI D A G _ _ hG U F _ _ _ F' _ _ _ σ k hk p
  refine ⟨qkExtExists R D.toPre F F' σ.toRingHom σ.commutes k p, fun x => ?_, fun p' x x' hp hx =>
    TorsionExt.qkToAkU_iff_of_qkExt firstFiveLaws R I hI D A G hG U F F' σ k hk p p' x x' hp hx⟩
  letI : Algebra F F' := σ.toRingHom.toAlgebra
  haveI : IsScalarTower (FractionRing R) F F' := IsScalarTower.of_algebraMap_eq fun c => (σ.commutes c).symm
  exact ⟨TorsionExt.fieldMap F F' ≫ x, rfl⟩

end GlobalTheory.UT.Cl
