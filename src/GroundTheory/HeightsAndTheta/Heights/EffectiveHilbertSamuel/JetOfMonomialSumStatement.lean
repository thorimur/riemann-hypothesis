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
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

def JetOfMonomialSum.Statement : Prop :=
  ∀ (n p : ℕ) (u : Fin p → (Fin n → ℂ) → ℂ) (h : (Fin p → ℕ) → (Fin n → ℂ) → ℂ)
    (z₀ : Fin n → ℂ) (a : ℕ),
    (∀ i, AnalyticAt ℂ (u i) z₀) → (∀ i, u i z₀ = 0) → (∀ α, AnalyticAt ℂ (h α) z₀) →
    (∀ k < a, iteratedFDeriv ℂ k
        (fun z => ∑ α ∈ Finset.Nat.antidiagonalTuple p a, (∏ i, u i z ^ α i) * h α z) z₀ = 0) ∧
    iteratedFDeriv ℂ a
        (fun z => ∑ α ∈ Finset.Nat.antidiagonalTuple p a, (∏ i, u i z ^ α i) * h α z) z₀ =
      ∑ α ∈ Finset.Nat.antidiagonalTuple p a,
        h α z₀ • iteratedFDeriv ℂ a (fun z => ∏ i, u i z ^ α i) z₀ ∧
    ∀ w : Fin n → ℂ, iteratedFDeriv ℂ a
        (fun z => ∑ α ∈ Finset.Nat.antidiagonalTuple p a, (∏ i, u i z ^ α i) * h α z) z₀
        (fun _ => w) =
      (a.factorial : ℂ) * ∑ α ∈ Finset.Nat.antidiagonalTuple p a,
        (∏ i, (fderiv ℂ (u i) z₀ w) ^ α i) * h α z₀

end GroundTheory.Heights₂.Heights.EffectiveHS
