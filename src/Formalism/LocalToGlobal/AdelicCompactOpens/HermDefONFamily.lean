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
import Mathlib.LinearAlgebra.Matrix.PosDef
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

namespace Formalism.L2.Props

open Matrix
open scoped ComplexOrder

def PolyDenseZero : Prop :=
  ∀ (σ : Type) [Fintype σ] (p : MvPolynomial σ ℂ) (S : Set (σ → ℂ)), Dense S →
    (∀ x ∈ S, MvPolynomial.eval x p = 0) → p = 0

def HermDefON : Prop :=
  ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ), G.PosDef → ∃ y : Matrix (Fin n) (Fin n) ℂ, IsUnit y.det ∧ yᴴ * G * y = 1

def HermConjExists : Prop :=
  ∀ (E : Type) [Field E] [CharZero E] (σ : E →+* E), (∀ x, σ (σ x) = x) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (J.map σ)ᵀ = J →
      ∃ P : Matrix (Fin n) (Fin n) E, (P.map σ)ᵀ * J * P = J.map σ

def DiagConj : Prop :=
  ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ),
    (∃ (P : GL (Fin n) ℂ) (d : Fin n → ℂ), (P : Matrix (Fin n) (Fin n) ℂ) * A * (P⁻¹ : GL (Fin n) ℂ) = diagonal d) →
    (∃ (P : GL (Fin n) ℂ) (d : Fin n → ℂ), (P : Matrix (Fin n) (Fin n) ℂ) * B * (P⁻¹ : GL (Fin n) ℂ) = diagonal d) →
    A.charpoly = B.charpoly →
    ∃ Q : GL (Fin n) ℂ, (Q : Matrix (Fin n) (Fin n) ℂ) * A * (Q⁻¹ : GL (Fin n) ℂ) = B

end Formalism.L2.Props
