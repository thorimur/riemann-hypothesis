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

namespace PI.Witt

def OneVector : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [CharZero K] [AddCommGroup V] [Module K V]
    (B : V →ₗ⋆[K] V →ₗ[K] K), (∀ x y, star (B x y) = B y x) →
    ∀ x y : V, B x x = B y y → B x x ≠ 0 →
      ∃ g : V ≃ₗ[K] V, (∀ z w, B (g z) (g w) = B z w) ∧ g x = y ∧
        ∀ z, B x z = 0 → B y z = 0 → g z = z

def Anisotropic : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [CharZero K] [AddCommGroup V] [Module K V]
    (B : V →ₗ⋆[K] V →ₗ[K] K), (∀ x y, star (B x y) = B y x) →
    ∀ U : Submodule K V, (∃ x ∈ U, ∃ y ∈ U, B x y ≠ 0) → ∃ x ∈ U, B x x ≠ 0

end PI.Witt
