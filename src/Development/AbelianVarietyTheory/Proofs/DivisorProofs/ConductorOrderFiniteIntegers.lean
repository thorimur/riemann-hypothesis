import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatModel

theorem finite_int_orderC : ∀ (E : Type) [Field E] [NumberField E] (c : Ideal (OF E)), Module.Finite ℤ (orderC c) := by
  intro E _ _ c
  have hint : ∀ x : orderC c, IsIntegral ℤ (x : E) := by
    intro x
    obtain ⟨a, b, -, h⟩ := mem_orderC.1 x.2
    have h2 : (x : E) = ((algebraMap (OF E) (𝓞 E) a + b : 𝓞 E) : E) := by
      rw [h]; first | rfl | (push_cast; rfl)
    rw [h2]
    exact RingOfIntegers.isIntegral_coe _
  let f : orderC c →ₗ[ℤ] 𝓞 E :=
    { toFun := fun x => ⟨x, hint x⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective f ?_
  intro x y hxy
  exact Subtype.ext (congrArg (fun z : 𝓞 E => (z : E)) hxy)

end GlobalTheory.LatModel
