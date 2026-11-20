import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

namespace Formalism.IndefR.Leaf

open Filter Topology

def SchurClosable : Prop :=
  ∀ (G H H' : Type) [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (π : G →* (H →L[ℂ] H)) (π' : G →* (H' →L[ℂ] H')),
    (∀ g x, ‖π g x‖ = ‖x‖) → (∀ g x, ‖π' g x‖ = ‖x‖) →
    (∀ B : H →L[ℂ] H, (∀ g, B.comp (π g) = (π g).comp B) → ∃ c : ℂ, B = c • ContinuousLinearMap.id ℂ H) →
    ∀ (D : Submodule ℂ H) (A : D →ₗ[ℂ] H'), Dense (D : Set H) →
      (∀ g, ∀ x ∈ D, π g x ∈ D) →
      (∀ g (x : D) (hx : π g x ∈ D), A ⟨π g x, hx⟩ = π' g (A x)) →
      (∀ (u : ℕ → D) (y : H'), Tendsto (fun n => (u n : H)) atTop (𝓝 0) →
        Tendsto (fun n => A (u n)) atTop (𝓝 y) → y = 0) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ x y : D, inner ℂ (A x) (A y) = (c : ℂ) * inner ℂ (x : H) (y : H)

end Formalism.IndefR.Leaf
