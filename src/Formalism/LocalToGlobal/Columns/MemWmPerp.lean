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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

noncomputable section

namespace Formalism.L2.Col

variable {K : Type} [Field K] [StarRing K] {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

def wmPerp (B : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule K V) : Submodule K V where
  carrier := {x | ∀ a ∈ A, B a x = 0}
  add_mem' := by
    intro x y hx hy a ha
    rw [map_add, hx a ha, hy a ha, add_zero]
  zero_mem' := by
    intro a _
    rw [map_zero]
  smul_mem' := by
    intro c x hx a ha
    rw [map_smul, hx a ha, smul_zero]

def wmZ (B : V →ₗ⋆[K] V →ₗ[K] K) (V₀ : Submodule K V) (θ : V →ₗ[K] W) : Submodule K V :=
  V₀ ⊓ wmPerp B (LinearMap.ker θ ⊓ V₀)

end Formalism.L2.Col
