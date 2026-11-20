import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.QkMul

open GlobalTheory.TorusExt
attribute [local instance] gtGroup

theorem exists_qk_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [Algebra (FractionRing R) F] (k d : ℕ) (p : QkPt D.toPre F k), ∃ q : QkPt D.toPre F (k * d), q.y = d • p.y ∧ q.g = p.g := by
  intro R _ _ _ D F _ _ k d p
  refine ⟨qkMk D.tau_bimult (d • p.y) p.g ?_, rfl, rfl⟩
  rw [mul_nsmul, qk_nsmul D.tau_bimult, map_nsmul]

end GlobalTheory.Mum.QkMul
