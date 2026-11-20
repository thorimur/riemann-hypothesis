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

namespace ReciprocityTheory.PGsh

open TensorProduct

universe u v w

def BadStatement : Prop :=
  ∀ (S : Type u) (A : Type v) [CommRing S] [CommRing A] [Algebra S A]
    (T₁ T₂ Q : Type w) [AddCommGroup T₁] [AddCommGroup T₂] [AddCommGroup Q]
    [Module S T₁] [Module S T₂] [Module S Q] [Module.Projective S Q]
    (ω₁ ω₂ Ω : Type w) [AddCommGroup ω₁] [AddCommGroup ω₂] [AddCommGroup Ω]
    [Module A ω₁] [Module A ω₂] [Module A Ω]
    (ι : T₁ →ₗ[S] T₂) (q : T₂ →ₗ[S] Q) (j : ω₁ →ₗ[A] ω₂) (p : ω₂ →ₗ[A] Ω)
    (α₁ : A ⊗[S] T₁ →ₗ[A] ω₁) (α₂ : A ⊗[S] T₂ →ₗ[A] ω₂) (β : A ⊗[S] Q →ₗ[A] Ω),
    Function.Injective ι → Function.Exact ι q → Function.Surjective q →
    Function.Injective j → Function.Exact j p →
    α₂ ∘ₗ ι.baseChange A = j ∘ₗ α₁ → p ∘ₗ α₂ = β ∘ₗ q.baseChange A → Function.Bijective β →
    (∀ c : A, (∀ x : ω₁, c • x ∈ LinearMap.range α₁) → ∀ x : ω₂, c • x ∈ LinearMap.range α₂) ∧
    Function.Injective (ι.baseChange A) ∧
    LinearMap.ker α₂ = (LinearMap.ker α₁).map (ι.baseChange A)

end ReciprocityTheory.PGsh
