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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace GlobalTheory.ConjugationEquiv

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def conjEquiv (N : Subgroup G) (b : G) (hb : ∀ u : G, u ∈ N ↔ b * u * b⁻¹ ∈ N) : N ≃ₜ* N where
  toFun u := ⟨b * (u : G) * b⁻¹, (hb u).1 u.2⟩
  invFun u := ⟨b⁻¹ * (u : G) * b, (hb _).2 (by
    have h : b * (b⁻¹ * (u : G) * b) * b⁻¹ = u := by group
    rw [h]; exact u.2)⟩
  left_inv u := Subtype.ext (by
    show b⁻¹ * (b * (u : G) * b⁻¹) * b = u
    group)
  right_inv u := Subtype.ext (by
    show b * (b⁻¹ * (u : G) * b) * b⁻¹ = u
    group)
  map_mul' u v := Subtype.ext (by
    show b * ((u : G) * v) * b⁻¹ = (b * u * b⁻¹) * (b * v * b⁻¹)
    group)
  continuous_toFun :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  continuous_invFun :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

@[simp] theorem coe_conjEquiv (N : Subgroup G) (b : G) (hb : ∀ u : G, u ∈ N ↔ b * u * b⁻¹ ∈ N)
    (u : N) : ((conjEquiv N b hb u : N) : G) = b * (u : G) * b⁻¹ := rfl

@[simp] theorem coe_conjEquiv_symm (N : Subgroup G) (b : G)
    (hb : ∀ u : G, u ∈ N ↔ b * u * b⁻¹ ∈ N) (u : N) :
    (((conjEquiv N b hb).symm u : N) : G) = b⁻¹ * (u : G) * b := rfl

end GlobalTheory.ConjugationEquiv
