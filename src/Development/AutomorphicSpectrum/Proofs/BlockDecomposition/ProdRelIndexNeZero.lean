import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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

namespace GlobalTheory.CompanionTheory.GroupIndex.RelProd

theorem relIndex_prod_eq_mul {G₁ G₂ : Type} [Group G₁] [Group G₂]
    (I₁ K₁ : Subgroup G₁) (I₂ K₂ : Subgroup G₂) :
    (I₁.prod I₂).relIndex (K₁.prod K₂) = I₁.relIndex K₁ * I₂.relIndex K₂ := by
  have hmap : ((I₁.prod I₂).subgroupOf (K₁.prod K₂)) =
      ((I₁.subgroupOf K₁).prod (I₂.subgroupOf K₂)).comap
        (Subgroup.prodEquiv K₁ K₂).toMonoidHom := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_prod, Subgroup.mem_comap]
    exact Iff.rfl
  unfold Subgroup.relIndex
  rw [hmap, Subgroup.index_comap_of_surjective _ (Subgroup.prodEquiv K₁ K₂).surjective,
    Subgroup.index_prod]

theorem relIndex_prod_ne_zero_of_ne_zero :
    ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] (I₁ K₁ : Subgroup G₁) (I₂ K₂ : Subgroup G₂),
      I₁.relIndex K₁ ≠ 0 → I₂.relIndex K₂ ≠ 0 → (I₁.prod I₂).relIndex (K₁.prod K₂) ≠ 0 := by
  intro G₁ G₂ _ _ I₁ K₁ I₂ K₂ h₁ h₂
  rw [relIndex_prod_eq_mul]
  exact mul_ne_zero h₁ h₂

end GlobalTheory.CompanionTheory.GroupIndex.RelProd
