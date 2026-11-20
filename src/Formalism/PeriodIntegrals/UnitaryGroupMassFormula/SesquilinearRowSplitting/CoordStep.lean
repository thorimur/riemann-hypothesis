import Mathlib.Algebra.Module.Lattice
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

open NumberField

namespace PI.SRW

def RepStep : Prop :=
  ∀ (E V : Type) [Field E] [NumberField E] [StarRing E] [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E), h.Nondegenerate →
    ∀ (Λ : Submodule (𝓞 E) V), Submodule.IsLattice E Λ →
    ∀ ℓ : Λ →ₗ[𝓞 E] E, ∃ w : V, ∀ x : Λ, h w x = ℓ x

def CoordStep : Prop :=
  ∀ (E V : Type) [Field E] [AddCommGroup V] [Module E V] (n : ℕ) (g : Fin n → V),
    LinearIndependent E g → ∃ c : Fin n → (V →ₗ[E] E), ∀ i j, c i (g j) = if i = j then 1 else 0

def RetrStep : Prop :=
  ∀ (E V : Type) [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] (Λ N : Submodule (𝓞 E) V), N ≤ Λ → Λ.FG →
    (∀ (o : 𝓞 E) (x : V), o ≠ 0 → x ∈ Λ → o • x ∈ N → x ∈ N) →
    ∃ ρ : Λ →ₗ[𝓞 E] V, (∀ x : Λ, ρ x ∈ N) ∧ ∀ x : Λ, (x : V) ∈ N → ρ x = x

end PI.SRW
