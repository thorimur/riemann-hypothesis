import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.PosFormProjection

theorem exists_orthogonal_coefficients :
    ∀ (g k : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ),
      (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm *ᵥ star z).re) →
      ∀ u : Fin k → Fin g → ℂ, LinearIndependent ℂ u →
      ∀ z : Fin g → ℂ, ∃ c : Fin k → ℂ,
        ∀ j, (z - ∑ i, c i • u i) ⬝ᵥ Hm *ᵥ star (u j) = 0 := by
  intro g k Hm hpos u hli z
  let A : (Fin k → ℂ) →ₗ[ℂ] (Fin k → ℂ) :=
    { toFun := fun c j => (∑ i, c i • u i) ⬝ᵥ Hm *ᵥ star (u j)
      map_add' := by
        intro a b
        funext j
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, add_dotProduct]
      map_smul' := by
        intro a b
        funext j
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul, ← Finset.smul_sum,
          smul_dotProduct] }
  have hinj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have hw : ∀ j, (∑ i, c i • u i) ⬝ᵥ Hm *ᵥ star (u j) = 0 := fun j => congrFun hc j
    have hww : (∑ i, c i • u i) ⬝ᵥ Hm *ᵥ star (∑ i, c i • u i) = 0 := by
      rw [star_sum, Matrix.mulVec_sum, dotProduct_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, hw j, smul_zero]
    have hw0 : ∑ i, c i • u i = 0 := by
      by_contra hne
      have := hpos _ hne
      rw [hww] at this
      simp at this
    funext i
    exact Fintype.linearIndependent_iff.mp hli c hw0 i
  obtain ⟨c, hc⟩ := LinearMap.injective_iff_surjective.mp hinj (fun j => z ⬝ᵥ Hm *ᵥ star (u j))
  refine ⟨c, fun j => ?_⟩
  have hcj : (∑ i, c i • u i) ⬝ᵥ Hm *ᵥ star (u j) = z ⬝ᵥ Hm *ᵥ star (u j) := congrFun hc j
  rw [sub_dotProduct, hcj, sub_self]

end GlobalTheory.CompanionTheory.Ar.PosFormProjection
