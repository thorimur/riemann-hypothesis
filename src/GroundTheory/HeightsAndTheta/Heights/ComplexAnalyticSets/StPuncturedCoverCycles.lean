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

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology Matrix

noncomputable section

def PuncturedCoverCycles.Statement : Prop :=
  ∀ (n e N : ℕ) (A : Matrix (Fin (e + 1)) (Fin n) ℂ) (c : Fin (e + 1) → ℂ) (r : ℝ)
    (X : Set (Fin n → ℂ)),
    0 < r → c 0 = 0 →
    (∀ x ∈ X, dist (A *ᵥ x) c < r ∧ (A *ᵥ x) 0 ≠ 0) →
    (∀ y : Fin (e + 1) → ℂ, dist y c < r → y 0 ≠ 0 → {x | x ∈ X ∧ A *ᵥ x = y}.encard = N) →
    (∀ x ∈ X, ∃ (O : Set (Fin (e + 1) → ℂ)) (V' : Set (Fin n → ℂ)) (g : (Fin (e + 1) → ℂ) → Fin n → ℂ),
      IsOpen O ∧ A *ᵥ x ∈ O ∧ IsOpen V' ∧ x ∈ V' ∧ DifferentiableOn ℂ g O ∧ g (A *ᵥ x) = x ∧
        (∀ y ∈ O, A *ᵥ g y = y) ∧ X ∩ V' = g '' O) →
    ∃ (m : ℕ) (ord : Fin m → ℕ) (ψ : Fin m → (Fin (e + 1) → ℂ) → Fin n → ℂ) (δ : ℝ),
      0 < δ ∧ δ ≤ 1 ∧ ∑ b, ord b = N ∧ (∀ b, 1 ≤ ord b) ∧
      (∀ b, DifferentiableOn ℂ (ψ b) (Metric.ball c δ ∩ {t | t 0 ≠ 0})) ∧
      (∀ b, ∀ t ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0},
        ψ b t ∈ X ∧ A *ᵥ ψ b t = Function.update t 0 (t 0 ^ ord b)) ∧
      (∀ b, Set.InjOn (ψ b) (Metric.ball c δ ∩ {t | t 0 ≠ 0})) ∧
      (∀ b b', b ≠ b' → ∀ t ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0},
        ∀ t' ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0}, ψ b t ≠ ψ b' t') ∧
      (∀ x ∈ X, dist (A *ᵥ x) c < δ ^ N →
        ∃ b, ∃ t ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0}, ψ b t = x)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
