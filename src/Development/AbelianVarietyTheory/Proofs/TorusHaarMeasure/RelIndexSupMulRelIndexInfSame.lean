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
import Mathlib.Topology.Sheaves.Presheaf

open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

theorem relIndex_sup_mul_relIndex_inf_same {A : Type} [AddCommGroup A] (M L N : AddSubgroup A)
    (h : M ≤ L) :
    (M ⊔ N).relIndex (L ⊔ N) * (M ⊓ N).relIndex (L ⊓ N) = M.relIndex L := by
  have h1 : (M ⊔ N).relIndex (L ⊔ N) = (M ⊔ (N ⊓ L)).relIndex L := by
    have e : L ⊔ N = L ⊔ (M ⊔ N) := by
      rw [← sup_assoc, sup_eq_left.mpr h]
    rw [e, AddSubgroup.relIndex_sup_right, ← AddSubgroup.inf_relIndex_right (M ⊔ N) L,
      sup_inf_assoc_of_le N h]
  have h2 : (M ⊓ N).relIndex (L ⊓ N) = M.relIndex (M ⊔ (N ⊓ L)) := by
    have e : M ⊓ N = M ⊓ (L ⊓ N) := by
      rw [← inf_assoc, inf_eq_left.mpr h]
    rw [e, AddSubgroup.inf_relIndex_right, AddSubgroup.relIndex_sup_left, inf_comm]
  rw [h1, h2, mul_comm]
  exact AddSubgroup.relIndex_mul_relIndex _ _ _ le_sup_left (sup_le h inf_le_right)

theorem relIndex_sup_mul_relIndex_inf :
    (∀ (A : Type) [AddCommGroup A] (M₁ L₁ M₂ L₂ : AddSubgroup A), M₁ ≤ L₁ → M₂ ≤ L₂ →
      (M₁ ⊔ M₂).relIndex (L₁ ⊔ L₂) * (M₁ ⊓ M₂).relIndex (L₁ ⊓ L₂) =
        M₁.relIndex L₁ * M₂.relIndex L₂) := by
  intro A _ M₁ L₁ M₂ L₂ h₁ h₂
  have a := relIndex_sup_mul_relIndex_inf_same M₁ L₁ M₂ h₁
  have b := relIndex_sup_mul_relIndex_inf_same M₂ L₂ L₁ h₂
  rw [sup_comm M₂, sup_comm L₂, inf_comm M₂, inf_comm L₂] at b
  rw [← a, ← b,
    ← AddSubgroup.relIndex_mul_relIndex (M₁ ⊔ M₂) (L₁ ⊔ M₂) (L₁ ⊔ L₂)
      (sup_le_sup_right h₁ _) (sup_le_sup_left h₂ _),
    ← AddSubgroup.relIndex_mul_relIndex (M₁ ⊓ M₂) (L₁ ⊓ M₂) (L₁ ⊓ L₂)
      (inf_le_inf_right _ h₁) (inf_le_inf_left _ h₂)]
  ring

end GlobalTheory
